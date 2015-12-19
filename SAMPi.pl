#!/usr/bin/env perl
#
# SAMPi - SAM4S (400, 500) ECR data reader, parser and logger (Last Modified 19/12/2015)
#
# This software runs in the background on a suitably configured Raspberry Pi,
# reads from a connected SAM4S ECR via serial connection, extracts various data,
# puts it into CSV format and stores it in preparation for upload via rsync or SFTP
#
# This software works in conjunction with the SAMPiD daemon to
# handle uploading CSV data files, removal of data older than 
# a configurable threshold and other supporting tasks
#
# SAMPi.pl can be automatically updated by uploading a newer version
# to a configurable update URL

# Modern Perl #

use 5.010;

use strict; 
use warnings;
use diagnostics;

# Imported Modules #

# Meta
use Carp; # Provides alternative warn and die functions
use Readonly; # Allows read-only constants
use constant::boolean; # Defines TRUE and FALSE constants, Perl lacks an explicit boolean type

# Misc
use Clone qw(clone); # Allows deep copying of nested hashes
use Data::Dumper; # Allows printing transaction data to screen for debugging
use Device::SerialPort; # Serial I/O 
use Digest::SHA1 qw(sha1_base64); # SHA1 checksum library
use LWP::Simple qw(getstore is_error $ua); # Used to download updates
use Storable; # Persistent hourly data
use Sys::Hostname; # Acquire hostname 
use Sys::RunAlone; # This module ensures only one instance of this software runs concurrently
use Text::Trim; # Remove leading and trailing whitespace
use Tie::IxHash; # Preserve the insertion order of hashes
use Time::HiRes qw(sleep); # Allows sleeping for less than a second

# File I/O
use Cwd qw(abs_path); # Get absolute path of currently executing script
use File::Basename; # Provides the dirname() function
use File::Compare; # Compare currently running script and downloaded script
use File::Copy; # Provides the copy function
use File::Spec qw(tmpdir); # Used to get portable directory paths
use File::Touch; # Perl implementation of the UNIX 'touch' command

# Globally accessible constants #

Readonly our $VERSION => '1.1.1';

Readonly my $MONITOR_MODE_ENABLED       => FALSE; # If enabled, SAMPi will not parse serial data and will simply store it
Readonly my $STORE_DATA_ENABLED         => TRUE;  # If enabled, SAMPi will store data for analysis, in addition to parsing it 
Readonly my $UPDATE_HOOK_ENABLED        => FALSE; # Attempt to call the postUpdate() function once on start if TRUE
Readonly my $LOGGING_ENABLED            => TRUE;  # Enable or disable logging info / warnings / errors to file
Readonly my $VERBOSE_PARSER_ENABLED     => FALSE; # If enabled, the parser will print information to STDOUT as it runs
Readonly my $DEBUG_ENABLED              => (@ARGV > 0) ? TRUE : FALSE; # If enabled, will read time solely from serial data
Readonly my $SAM4S_520                  => (-e "./config/520") ? TRUE : FALSE; # Use 520 specific code where necessary

Readonly my $DIRECTORY_SEPARATOR        => ($^O =~ /^Win/ix) ? "\\" : "/"; # Ternary operator used for brevity, included for future W32 compatability
Readonly my $CURRENT_VERSION_PATH       => abs_path($0);
Readonly my $LATEST_VERSION_PATH        => File::Spec->tmpdir() . $DIRECTORY_SEPARATOR . "SAMPi.pl";
Readonly my $UPDATE_CHECK_DELAY_MINUTES => 120; # Check for updates every two hours in idle mode
Readonly my $TRANSACTION_DELAY_SECONDS  => 1200; # Seconds to wait for a header in a new hour before saving previous hour (used to detect last hour of data)
Readonly my $SINGLE_ITEM_LIMIT          => 200; # Maximum acceptable price for one item in a transaction, if a value above this is read it will be ignored
Readonly my $LOG_FILENAME               => "sampi.log"; # Filename to use for the log created by SAMPi when logging is enabled

# Define opening and closing hours
Readonly my $STORE_OPENING_HOUR_24 => 6;
Readonly my $STORE_CLOSING_HOUR_24 => 23;

# Localisation
Readonly my $CURRENCY_SYMBOL => '£';

# Constants used to identify which part of the data we are currently parsing
Readonly my %PARSER_EVENTS =>
(
    "HEADER" => 1,
    "TRANSACTION" => 2,
    "OTHER" => 3,
    "FOOTER" => 4
);

# Header format differs between 420 and 520 output, 420 includes date / time information
Readonly my $HEADER_REGEX => (!$SAM4S_520) ? qr/^\d{1,2}\/\d{2}\/\d{4}/x : qr/REGISTER\sMODE/x;

# Dispatch table (array of hashes) to simplify parsing and remove the need for long if-else chains
# Links a regex, which matches a line of data, to the action to call when a match is discovered 
Readonly my @EVENT_DISPATCH_TABLE => 
(
    {
        parser => \&parseHeader,
        regexp => $HEADER_REGEX, # Defined above, the header for the 420 is more verbose than the 520 output we are able to receive
    },
    {
        parser => \&parseFooter,
        regexp => qr/^CLERK/x, # Begins with "CLERK", delimits 420 transactions (although reprints are printed beneath this line)
    },
    {
        parser => \&parseReport,
        regexp => qr/REPORT/x, # Contains "REPORT", 420 only
    },
    {
        parser => \&parseCancel,
        regexp => qr/CANCEL/x, # Contains "CANCEL"
    },
    {
        parser => \&parseReprint,
        regexp => qr/REPRINT/x, # Contains "REPRINT"
    },
    {
        parser => \&parseRefund,
        regexp => qr/^PAID\sOUT/x, # Begins with "PAID OUT"
    },   
    {
        parser => \&parseNoSale,
        regexp => qr/(NOSALE|NS)/x, # Contains "NOSALE", these need to be recorded
    },
    {
        parser => \&parseDiagnostic,
        regexp => qr/=/x, # Contains '=', used to delimit blocks of diagnostics
    }
);

# Similar dispatch table for processing various transaction data, some functions only apply to the 420
Readonly my @TRANSACTION_DISPATCH_TABLE =>
(
    {
        parser => \&adjustTotal,
        regexp => qr/TOTAL/x, # Contains "TOTAL"
    },
    {
        parser => \&adjustCashTotal, # Wrapper for adjustTotal()
        regexp => qr/CASH/x, # Contains "CASH"
    },

    {
        parser => \&adjustChange, # Could use a flag for adjustTotal() but complete separation is cleaner
        regexp => qr/CHANGE/x, # Contains "CHANGE"
    },
    {
        parser => \&adjustCardTotal, # Also a wrapper for adjustTotal()
        regexp => qr/(CHEQUE|CARD)/x, # Contains "CHEQUE" or "CARD"
    },
    {
        parser => \&adjustDiscount, # Handle discounts
        regexp => qr/^AMOUNT/x, # Begins with "AMOUNT", represents a discount 
    }
);

# Globally accessible variables, these variables are used by multiple functions 
# and will be refactored in future versions to follow best practices 

# File I/O & Flags
my $csvFile; # CSV file descriptor, used for output from SAMPi
my $csvOpen = FALSE; # Flag which determines whether a csv output file is currently open
my $serialLog; # Serial log descriptor (monitor mode only)
my $dataOpen = FALSE; # Determines if serial log file has been opened (if data logging is enabled)
my $dataLogFilePath; # File path for logged serial data, cleared daily when SAMPi goes into idle mode

# Parser State
my $previousEvent = $PARSER_EVENTS{OTHER}; # Track the previous event, used for counting transactions
my $previousEventTime = "0"; # Stores the time of the previous event (in  a string)
my $currentEvent = $PARSER_EVENTS{OTHER}; # Tracks the current type of data being parsed
my $currentEventTime = "0"; # Store the time of the current event (in a string)
my $currentEventHour = "0"; # Just the hour portion of the current event time
my $lastSavedHour = "0"; # Store the hour we last saved when reading time from the system clock
my $currentPLU; # Store the current PLU, used when applying discounts 
my $previousEventInvalid = FALSE; # Flag which prevents reprints and cancellations from being counted as the first / last event
my $prevTransactionTime = 0; # Stores time of most recently read transaction, checked in order to save at the end of the day

# 500 Series Variables
my @dataBuffer; # Buffer for stored serial data, required for 520 parsing
my $ignoreHeaders = FALSE; # Required to allow cancellations to work correctly

# The following hash will contain the list of recognised PLUs, these will be read in from a file
# We tie this hash to preserve the insertion order for later use in CSV columns, saves front-end work
my  %PLUList;
tie %PLUList, "Tie::IxHash";

# The following data structure holds data for each of the columns that will eventually comprise the CSV file
# We store transactions as we read them, make calculations from this data and convert it to CSV once hourly
# This hash is tied for the same reason as the PLU list.
my  %hourlyTransactionData;
tie %hourlyTransactionData, "Tie::IxHash";

# Initial values are set to zero
%hourlyTransactionData =
(
    "Hours"             => "0",
    "Total Takings"     => "0",
    "Cash"              => "0",
    "Credit Cards"      => "0",
    "PLU"               => \%PLUList,
    "Customer Count"    => "0",
    "First Transaction" => "0",
    "Last Transaction"  => "0",
    "No Sale"           => "0"
);

# Copy for reverting to if required
my  %hourlyTransactionDataCopy;
tie %hourlyTransactionDataCopy, "Tie::IxHash";

# Signals #

$SIG{USR1} = sub { print Dumper(\%hourlyTransactionData); }; # Print %hourlyTransactionData on demand

# Functions #

# Utility function which returns the current date as an array in [yyyy][mm][dd] format
sub getCurrentDate
{
    my @timestamp = localtime();
    
    my $currentYear  = $timestamp[5] + 1900; # Need to add 1900 to get the current year
    my $currentMonth = $timestamp[4] + 1; # Months from localtime() are zero-indexed
    my $currentDay   = $timestamp[3];

    my @currentDate = ($currentYear, $currentMonth, sprintf("%02d", $currentDay)); # Pad day

    return @currentDate;
}

# Utility function to return the current hour from the system clock in 24-hour format
sub getCurrentHour
{
    my (undef, undef, $currentHour) = localtime();

    return sprintf("%02d", $currentHour); # Return with leading zero if hour < 10
}

# Simple function to print logging messages  with a timestamp to a file and / or stdout 
sub logMsg
{
    # Take the message passed in as the first parameter and get the current time and date
    my ($logMessage) = @_;
    my $timestampStr = localtime();

    # Write message to file if logging is enabled
    if ($LOGGING_ENABLED)
    {
        state $logFile; # File descriptor for the log file we have created or are about to create
        state $logOpen = FALSE; # Static flag to determine if the log file has been opened during the current execution

        unless ($logOpen)
        {
            # Attempt to open the log file (located in the 'log' subdir of the current directory) in append mode
            ## no critic qw(RequireBriefOpen)
            unless (open ($logFile, '>>', "log" . $DIRECTORY_SEPARATOR . $LOG_FILENAME))
            {
                die("Error opening log file at ." . $DIRECTORY_SEPARATOR . "log" . $DIRECTORY_SEPARATOR . "$LOG_FILENAME\n");
            }

            $logFile->autoflush(1); # Disable buffering
            $logOpen = TRUE;
        }

        # Write message with timestamp to the log file
        print $logFile "$timestampStr: $logMessage\n";
    }

    # Print the message to STDOUT in any case
    print "$timestampStr: $logMessage\n";

    return;
}

# This function initialises the serial port with the correct settings
sub initialiseSerialPort
{
    # Get correct file descriptor
    Readonly my $SERIAL_PORT => ($^O =~ /Linux/i) ? "/dev/ttyUSB0" : "/dev/tty.usbserial"; # This varies depending on current OS
    #Readonly my $SERIAL_PORT => "/dev/ttys008"; # Virtual serial port

    # 8N1 with software flow control by default
    Readonly my $BPS => ($DEBUG_ENABLED || $SAM4S_520) ? 115200 : 9600; # Higher baud rate for debugging or newer ECR
    Readonly my $DATA_BITS => 8;
    Readonly my $STOP_BITS => 1;
    Readonly my $PARITY => "none";
    Readonly my $HANDSHAKE => "none";

    logMsg("Initialising Serial Port...");
    my $serialPort = Device::SerialPort->new($SERIAL_PORT);

    # If there is an error initialising the serial port, print a warning and terminate
    unless (defined $serialPort)
    {
        logMsg("Error opening serial port $SERIAL_PORT: $!\n"); 
        die "Error opening serial port $SERIAL_PORT: $!\n";
    }

    $serialPort->baudrate($BPS);
    $serialPort->databits($DATA_BITS);
    $serialPort->stopbits($STOP_BITS);
    $serialPort->parity($PARITY);
    $serialPort->handshake($HANDSHAKE);

    if ($SAM4S_520)
    {
        # The data available from the 520 is not well-delimited, so we match ASCII escape characters
        $serialPort->are_match("\e", "-re", "*CANCEL*", "-re", "CHANGE\\s\\d{1,2}\.\\d{2}"); # Also match CANCEL notice "CHANGE\s£x.xx" as delimiters
    }

    else
    {
        # Set lookfor() to match EOL characters so that we can read data line by line
        $serialPort->are_match("\r", "\n");
    }

    $serialPort->lookclear;  

    logMsg("Opened serial port $SERIAL_PORT at $BPS" . "BPS");

    return $serialPort; # Return valid Device::SerialPort object to the caller for use
}

# This utility function returns TRUE (provided by constant::boolean) if the current time is during business hours
# This will affect the behaviour of the script, it will either be in data gathering mode or idle / update mode
sub isBusinessHours
{
    my $currentHour = getCurrentHour();

    state $idleMode = FALSE; # Keep track of whether we are in idle mode or not

    # Return true if we are within business hours
    if ($currentHour >= $STORE_OPENING_HOUR_24 && $currentHour <= $STORE_CLOSING_HOUR_24)
    {
        if ($idleMode)
        {
            logMsg("Exiting Idle Mode");
            $idleMode = FALSE;
        }

        return TRUE;
    }

    # Or false otherwise
    else
    {
        unless ($idleMode || $VERBOSE_PARSER_ENABLED || $DEBUG_ENABLED) # Ignore idle mode if debugging parser
        {
            if (defined $csvFile)
            {
                close $csvFile; # Close the CSV file handle for the days' transactions
                $csvOpen = FALSE;
            }

            if (defined $serialLog)
            {
                close $serialLog;
                unlink $dataLogFilePath;
                $dataOpen = FALSE;
            }

            logMsg("Entering Idle Mode");
            clearData(); # Clear the stored data
            unlink <hourlyData*>;  # Remove any stray hourly data 
            $idleMode = TRUE;
        }

        # If we are debugging the parser we want to disable idle mode
        return FALSE unless $VERBOSE_PARSER_ENABLED; 

        return TRUE;
    }
}

# This function calls the isUpdateAvailable() function and returns the value to the caller
# Updates will be checked for at startup and during idle mode
sub checkForUpdate
{
   # Check if the current script and latest script on the server differ
    my $updateAvailable = isUpdateAvailable();

    if ($updateAvailable)
    {
        # Install the newer version of the script and run it
        logMsg("Newer version is available, updating and restarting");
        updateAndReload($updateAvailable);
    }

    return $updateAvailable;
}

# This function checks to see if a new version is available and returns true if this is the case
sub isUpdateAvailable
{   
    Readonly my $UPDATE_URL => "https://dl.dropboxusercontent.com/u/12186225/SAMPi.pl";

    logMsg("Checking for update...");
    logMsg("Attempting to download from update URL... ($UPDATE_URL)");

    # Save the latest available version in a temporary directory, timeout is 30 seconds
    $ua->timeout(30);
    my $downloadStatus = getstore($UPDATE_URL, $LATEST_VERSION_PATH);

    # If the download failed then write a message to the log and return without an update
    if (is_error($downloadStatus)) 
    {
        logMsg("Error downloading update from $UPDATE_URL");
        return FALSE;
    }

    # Compare the current software and the newest version
    # If they differ then the donloaded version is newer
    if (compare ($CURRENT_VERSION_PATH, $LATEST_VERSION_PATH) == 1) 
    {
        # So we report this availability to the caller 
        return TRUE;
	}

    else
    {
        # Otherwise return false indicating that no update was found
        return FALSE;
    }
}

# This function overwrites the currently executing script with the new version downloaded
# in the isUpdateAvailable() function
sub updateAndReload
{
    my ($updateAvailable) = @_;

    if ($updateAvailable)
    {
        logMsg("Update found, overwriting $CURRENT_VERSION_PATH with $LATEST_VERSION_PATH");
        copy($LATEST_VERSION_PATH, $CURRENT_VERSION_PATH);
        logMsg("Restarting...");

        # Remove file which signifies we have run postUpdate() before if it exists
        if (glob("*.run"))
        {
            unlink <*.run>; 
        }

        exec $0; # Exec call replaces the currently running process with the new version
    }

    else
    {
        croak("updateAndReload() should not be called if there is no update available");
    }

    return;
}

# This function is only called if the $RUN_UPDATE_HOOK constant is set to TRUE
# It is used in cases where an operation needs to be performed once after an update
# Such as changing a system setting on every Pi in the SAMPi network simultaneously
sub postUpdate
{
    # Enter whatever code you need to execute in the $postUpdateCode variable below
    my $postUpdateCode = "";

    unless ($postUpdateCode) # Ensure $postUpdateCode is not empty
    {
        return;
    }

    # Generate checksum for requested post-update code, this prevents it running more than once per version
    my $checksum = sha1_base64($postUpdateCode);
    $checksum =~ s/$DIRECTORY_SEPARATOR/-/xg; # Replace anything matching the directory separator

    my $postUpdateExecuted = dirname($CURRENT_VERSION_PATH) . $DIRECTORY_SEPARATOR . $checksum . ".run";

    if (! -f $postUpdateExecuted) # If postUpdate() has not been called before (semaphore does not exist)
    {
        logMsg("postUpdate() call requested, executing postUpdateCode");

        # String eval is not recommended but is the only way to run this code dynamically
        ## no critic qw(ProhibitStringyEval)
        my $postUpdateValid = eval $postUpdateCode;

        # Detect errors and log accordingly
        if (not defined $postUpdateValid)
        {
            chomp($@);
            logMsg("Error in postUpdateCode: $@");
        }

        touch $postUpdateExecuted; # Create semaphore to prevent repeat execution
    }

    else
    {
        logMsg("postUpdate() called previously, ignoring. Recommend setting \$UPDATE_HOOK_ENABLED to FALSE");
    }
    
    return;
}

# This function manages the saving of hourly data to persistent storage
# It sets the last transaction time, generates the CSV data
# and clears data structures 
sub saveData
{
    # Guard against saving on startup
    unless ($currentEventTime eq "0")
    {
        # Set the last transaction time
        $hourlyTransactionData{"Last Transaction"} = $previousEventTime;

        # Fix disparities between the total takings and the cash total
        if ($hourlyTransactionData{"Credit Cards"} == 0)
        {
            $hourlyTransactionData{"Total Takings"} = $hourlyTransactionData{"Cash"};
        }

        # Write the collected data to the CSV file and clear the data structure
        generateCSV();
        clearData();
    }

    # Set the last saved hour (indicates that we do not need to save again until the hour changes)
    $lastSavedHour = $currentEventHour;

    return;
}

# This function correctly sets the $previousEvent variable depending on the current event
sub setPreviousEvent
{
    if ($currentEvent == $PARSER_EVENTS{OTHER})
    {
        $previousEvent = $PARSER_EVENTS{OTHER};
    }

    elsif ($currentEvent == $PARSER_EVENTS{TRANSACTION})
    {
        $previousEvent = $PARSER_EVENTS{TRANSACTION};
    }

    return;
}

# This function is part of the parser, it processes headers.
# Each header represents a separate event (transaction or report)
# and includes a timestamp which is extracted and stored for later use
sub parseHeader
{
    my ($headerLine) = @_;

    # Ignore headers if we are on a 520 and in the middle of a transaction
    if ($SAM4S_520 && $ignoreHeaders)
    {
        return;
    }

    # Make a copy of the current transaction data so we can revert if required
    saveState();

    # Print out the most recently processed transaction if we are in verbose mode
    if ($previousEvent == $PARSER_EVENTS{TRANSACTION} && $VERBOSE_PARSER_ENABLED)
    {
        print Dumper(\%hourlyTransactionData);
    }    
    
    # Store the time of the previous event if there is one, as long as it was a valid transaction
    if ($currentEventTime ne "0" && $currentEvent != $PARSER_EVENTS{OTHER} && !$previousEventInvalid)
    {
        # Used to set the last transaction time for each hour
        $previousEventTime = $currentEventTime;
    }

    $previousEventInvalid = FALSE; # Clear invalid event flag
    $prevTransactionTime = time(); # Set the time of the previous transaction in UNIX format

    # Check for a time in the header variable, if so we are connected to a 420
    if ($headerLine =~ /([0-9][0-9]:[0-9][0-9])/)
    {
        $currentEventTime = $1; 
    }

    # Otherwise we are connected to a 520 and need to use the system clock instead of the time from the till
    elsif ($SAM4S_520)
    {
        my (undef, $currentMinute, $currentHour) = localtime();
        $currentEventTime = sprintf("%02d:%02d", $currentHour, $currentMinute);
        $ignoreHeaders = TRUE; # Ignore erroneous header messages
    }

    # Otherwise we are not inside a valid header line
    else
    {
        logMsg("Unidentified header detected: $headerLine");
        return;
    }

    # Get just the hour
    $currentEventHour = substr($currentEventTime, 0, 2);

    # When we have finished gathering data for the hour, we need to take it and write it out to the CSV file
    # If we are debugging, we only use the hours in the serial headers to indicate the current hour so that
    # we don't have to wait until the clock hour changes to generate CSV data. In production we check both times

    # If the current hour is different to the hour of the most recent transaction and this is not the beginning of the day...
    if ($hourlyTransactionData{"Hours"} ne "0" && $currentEventHour > substr($hourlyTransactionData{"Hours"}, 0, 2))
    {
        saveData(); 
    }

    # If no first transaction has been logged for the current hour
    if ($hourlyTransactionData{"First Transaction"} eq "0")
    {
        # Set the 'Hours' field accordingly, in the format "HH.00 - (HH+1).00"
        my $nextHour = sprintf("%02d", $currentEventHour+1);
        $hourlyTransactionData{"Hours"} = sprintf("%02d.00-%02d.00", $currentEventHour, $nextHour);

        # Store the time of the first transaction
        $hourlyTransactionData{"First Transaction"} = $currentEventTime;           
    }

    if ($VERBOSE_PARSER_ENABLED)
    {
        print "HEADER AT $currentEventTime\n";
    }    
    
    # Set the current parser state
    $currentEvent = $PARSER_EVENTS{HEADER};
    
    if ($SAM4S_520)
    {
        $ignoreHeaders = TRUE; # Ignore subsequent 'headers' until we reach the end of a transaction
    }

    return;
}

# This function is called when detecting a footer
# It notifies the parser that it is no longer processing 
# a transaction and may save when required
sub parseFooter
{
    unless ($currentEvent == $PARSER_EVENTS{OTHER})
    {
        $currentEvent = $PARSER_EVENTS{FOOTER};
    }

    if ($VERBOSE_PARSER_ENABLED)
    {
        print "FOOTER AT $currentEventTime\n";
    }    

    return;
}

# This function is called when a report header is matched in the incoming data. It does not currently do anything
# As reports are ignored in the current implementation in favour of manually calculating totals
# In the future this function could be used to read specific data from reports and act on it
sub parseReport
{
    if ($VERBOSE_PARSER_ENABLED)
    {
        print "REPORT AT $currentEventTime\n";
    }

    $currentEvent = $PARSER_EVENTS{OTHER};
    return;
}

# This is one of several short functions for parsing transactions, this function adjusts the total for card, cash or overall
# depending on the value of the second parameter passed in
sub adjustTotal
{
    my ($transactionValue, $totalFor) = @_;

    if (not defined $totalFor)
    {
        # 520 customer count is incremented in the 'CHANGE' parser
        unless ($SAM4S_520)
        {
            # Increment the transaction count, can decrement later if we read a cancel or a reprint
            $hourlyTransactionData{"Customer Count"}++; 
        }

        # Overall total will be adjusted
        $totalFor = "Total Takings"; 
    }
        
    # Add to or subtract (in void mode) from the desired total according to the value of the second parameter
    $hourlyTransactionData{$totalFor} += $transactionValue;

    return;
}

# Handle Cash Total
sub adjustCashTotal 
{
    my ($cashTotal) = @_;
    adjustTotal($cashTotal, "Cash");
    return;
}

# Handle Change
sub adjustChange
{
    my ($changeValue) = @_;

    if ($currentPLU =~ "CARD:") # Change should not follow a card transaction, handle cashiers hitting 'CARD' instead of 'CASH'
    {
        logMsg("Change detected after card transaction, correcting...");
        my $adjustedAmount = (split(':', $currentPLU, 2))[1]; # Get value of erroneous card transaction
        $hourlyTransactionData{"Credit Cards"} -= $adjustedAmount; # Subtract value erroneously added to card total
        $hourlyTransactionData{"Cash"} += $adjustedAmount; # Add it to cash where it should be
    }

    if ($SAM4S_520)
    {
        $hourlyTransactionData{"Customer Count"}++;  # Increment customer count when reaching 'change' on the 520, last element of a transaction
        $changeValue =~ s/$CURRENCY_SYMBOL//g; # Remove the currency symbol before we subtract

        if ($ignoreHeaders)
        {
            $ignoreHeaders = FALSE; # We have reached the end of a transaction so we can listen for headers again
        }
    }

    $hourlyTransactionData{"Cash"} -= $changeValue; # Remove change from cash total

    return;
}

# Handle the card total field
sub adjustCardTotal
{
    my ($cardTotal) = @_;
    adjustTotal($cardTotal, "Credit Cards");
    $currentPLU = "CARD:$cardTotal"; # Record value if hit accidentally
    return;
}

# This function accounts for discounted products and ensures PLU totals correctly add up to the overall total
sub adjustDiscount
{
    my ($discountValue) = @_;
    print "Adjusting $currentPLU total for discount of $discountValue\n";
    $hourlyTransactionData{"PLU"}{$currentPLU} += $discountValue;

    return;
}

# This function parses transactions, each is part of a group and contains the PLU and price for one or more items. 
# These are processed as key-value pairs with validation to remove lines that are invalid or do not represent PLUs (e.g. totals)
# Similarly to the parseChunk() function, this function makes use of a dispatch table instead of a long if-elsif-else construct
sub parseTransaction
{
    my ($transactionLine) = @_;

    # Ensure we are expecting a transaction and the line contains a price
    if ($currentEvent != $PARSER_EVENTS{HEADER} && $currentEvent != $PARSER_EVENTS{TRANSACTION} ||
        index($transactionLine, $CURRENCY_SYMBOL) == -1) 
    {
            return unless ($transactionLine =~ /^AMOUNT/x); # Discount values do not have a currency symbol
            $transactionLine =~ s/-/$CURRENCY_SYMBOL-/gx; # Add the currency symbol so the line works with the parser
    }
    
    $currentEvent = $PARSER_EVENTS{TRANSACTION};

    # Separate the data into a key (PLU or label) and a value (e.g. price or total) to use as input for the transaction parser
    my ($transactionKey, $transactionValue) = split($CURRENCY_SYMBOL, $transactionLine, 2);

    # Search the dispatch table for a suitable parser for the given $transactionKey
    # This only applies to keys which are not product PLUs (e.g. totals)
    foreach my $transactionKeyType (@TRANSACTION_DISPATCH_TABLE) 
    {
        if ($transactionKey =~ $transactionKeyType->{regexp}) 
        {
            # Call the appropriate parsing function with the label's value as the parameter
            $transactionKeyType->{parser}->($transactionValue);
            return;
        }
    }

    # If no key-specific parsing function was found, we are processing a simple "PLU => COST" transaction
    # We need to perform validation and ensure that the key is a valid PLU and then adjust the total for
    # the PLU in question
    trim($transactionKey); # Remove leading and trailing spaces
    $transactionKey =~ s/(\w+)/\u\L$1/gx; # Normalise PLU case to "Title Case"

    # Ensure the PLU matches one of the valid PLU names
    if (exists($PLUList{$transactionKey}))
    {
        if ($transactionValue < $SINGLE_ITEM_LIMIT)
        {
            # Add the transaction value to the hourly total for this PLU
            $hourlyTransactionData{"PLU"}{$transactionKey} += $transactionValue; 
            $currentPLU = $transactionKey;

            # Increment total (520 only, parser waits for TOTAL line on the 420)
            if ($SAM4S_520)
            {
                adjustTotal($transactionValue); 
            }
        }

        else
        {
            adjustTotal(-$transactionValue); # Ignore this item in the total for this transaction
            adjustCashTotal(-$transactionValue); # As well as the cash total
            logMsg("$transactionKey at $CURRENCY_SYMBOL$transactionValue appears to be erroneous, if this is a genuine transaction increase \$SINGLE_ITEM_LIMIT");
        }
    }

    else
    {
        logMsg("\"$transactionKey\" is not a valid PLU, ignoring");
    }

    if ($VERBOSE_PARSER_ENABLED)
    {
        print "\tITEM FOR TRANSACTION $hourlyTransactionData{'Customer Count'} at $transactionValue\n";
        ($SAM4S_520 && $VERBOSE_PARSER_ENABLED) ? print Dumper(\%hourlyTransactionData) : 0; # Print debug info for 520
    }

    return;
} 

# This function parses NOSALE messages, these occur when people open the till without processing a transaction
# These should be logged for security and training purposes
sub parseNoSale
{
    logMsg("Till opened but no transaction processed at $currentEventTime");   
    $hourlyTransactionData{"No Sale"}++;
    return;
}

# This function parses cancelled transactions and handles resetting the current state of the data
sub parseCancel
{
    logMsg("Ignoring cancelled transaction at $currentEventTime");
    loadState(); # Reset to previously saved state

    return;
}

# Similar to the above 
sub parseReprint
{
    logMsg("Ignoring reprinted transaction at $currentEventTime");
    loadState();

    return;
}

# This function parses refunds, these are not currently implemented in SAMPi but may be in the future
sub parseRefund
{
    logMsg("SAMPi does not currently implement refund tracking, ignoring");
    $currentEvent = $PARSER_EVENTS{OTHER};
    return;
}

# This function parses diagnostic information (e.g. settings), this is currently ignored but logged
sub parseDiagnostic
{
    unless ($currentEvent == $PARSER_EVENTS{OTHER}) # Only need to call this once before we set the parser to ignore
    {
        # Ignore settings and diagnostic information
        logMsg("Ignoring diagnostic output: $_[0]");
        $currentEvent = $PARSER_EVENTS{OTHER};
        return;
    }
}

# This function is responsible for parsing a unit of serial data and storing various information which is later converted to CSV
# A dispatch table is used in preference to a long if-elsif-else chain as it is more efficient and easier to maintain
sub parseChunk
{
    # The chunk (line or section) of data passed in as a parameter will be accessible as $dataChunk
    my ($dataChunk) = @_;

    # Additional debugging for 500 Series
    if ($SAM4S_520 && $DEBUG_ENABLED)
    {
        print "RECEIVED: $dataChunk\n";
    }

    # Remove any errant hex values or question marks returned by the serial port
    # This function makes more drastic changes to the 520 data due to the poor parsability
    $dataChunk = normaliseData($dataChunk);

    # Set previous event correctly depending on type of last processed data line
    setPreviousEvent();

    # Match the current line with the entry for its data type in the dispatch table
    # Lines matching a header will call parseHeader(), etc.
    foreach my $dataType (@EVENT_DISPATCH_TABLE) 
    {
        if ($dataChunk =~ $dataType->{regexp}) 
        {
            # Call the appropriate parsing function with the current line as a parameter
            $dataType->{parser}->($dataChunk);
            return;
        }
    }

    # If nothing in the dispatch table matched, we could be dealing with a transaction
    # More validation is performed within the function to check if this is the case
    parseTransaction($dataChunk);

    return;
}

# This function saves the current state of the hourly transaction data in case
# it needs to be returned to after reading a cancelled or reprinted transaction
sub saveState
{
    %hourlyTransactionDataCopy = %{ clone(\%hourlyTransactionData) };

    # Serialise the data structure so we can resume from here in case of a short-term power failure, etc.
    unless ($currentEventHour eq "0") # Do not attempt to store data on startup when nothing has been read
    {
        store(\%hourlyTransactionDataCopy, "hourlyData_$currentEventHour.dat");
    }

    return;
}

# This function loads a previously saved state and is used for returning to
# a "known-good" state after the previous transaction was declared as invalid
# due to being a reprint, cancellation or other voided transaction
sub loadState
{
    # Reset the state of the hourly transaction data to how it was before the current transaction
    $previousEventInvalid = TRUE;
    %hourlyTransactionData = %hourlyTransactionDataCopy;

    unless ($currentEvent == $PARSER_EVENTS{FOOTER}) # XXX: This may not be required
    {
        $currentEvent = $PARSER_EVENTS{OTHER};
    }

    return;
}

# This function is called when SAMPi is operating in monitor (non-parsing) mode
# It will save the given line of serial data to a serial log file for later use
## no critic qw(RequireBriefOpen)
sub storeLine
{
    my ($dataChunk) = @_;

    my @date = getCurrentDate();
    $dataLogFilePath = $ENV{'HOME'} . $DIRECTORY_SEPARATOR . "serial_log_" . $date[2] . ".dat"; 

    unless ($dataOpen)
    {
        unless (open ($serialLog, '>>', $dataLogFilePath))
        {
            logMsg("Error opening serial log file at $dataLogFilePath");
            die;
        }

        logMsg("Opened serial data log at $dataLogFilePath");
        $serialLog->autoflush(1); # Disable output buffering
        $dataOpen = TRUE;
    }

    print $serialLog $dataChunk;

    return;
}

# This function resets the hourlyTransactionData hash to ready it for another hour's worth of data
sub clearData
{
    # Iterate over the transaction data hash
    foreach my $key (keys %hourlyTransactionData)
    {
        # Iterate over the nested PLU hash
        if ($key eq "PLU")
        {
            foreach my $PLU (keys %{ $hourlyTransactionData{$key} })
            {
                # Reset the total for each PLU
                $hourlyTransactionData{$key}{$PLU} = "0";
            }
        }

        else
        {
            # Reset other values
            $hourlyTransactionData{$key} = "0";
        }
    }

    # Remove serialised data for the previous hour
    unlink <hourlyData*>; 

    return;
}

# This function converts the collected hourly data to CSV format for later upload to the front-end server via rsync or SFTP
sub generateCSV
{
    state $lastCalledHour = 0; # Keep track of when this function was last called to prevent duplicate entries in the file

    # Create an appropriately named CSV file and open it in append mode if it does not already exist
    unless ($csvOpen)
    {
        initialiseOutputFile();
    }

    # Sanity check, do not generate a row of CSV if there were no transactions in the previous hour
    if ($hourlyTransactionData{"Total Takings"} eq "0" || $hourlyTransactionData{"Customer Count"} <= 0)
    {
        logMsg("No transactions read for " . $hourlyTransactionData{"Hours"} . ", discarding CSV"); 
        return;
    }

    # Similarly, do not print to file if we already have data for the current event hour in the file
    if ($lastCalledHour == $currentEventHour)
    {
        unless (time() - $prevTransactionTime > $TRANSACTION_DELAY_SECONDS)
        {
            logMsg("generateCSV() has already been called for $currentEventHour, not generating");
            return;
        }
    }
    
    logMsg("Generating CSV for " . $hourlyTransactionData{"Hours"});

    # Iterate through the hourly transaction data
    foreach my $transactionDataKey (keys %hourlyTransactionData)
    {
        my $transactionData = $hourlyTransactionData{$transactionDataKey};

        # Process PLU totals
        if ($transactionDataKey eq "PLU")
        {
            # Iterate over the nested hash and extract the saved data
            foreach my $PLU (keys %{ $hourlyTransactionData{$transactionDataKey} })
            {
                $transactionData = $hourlyTransactionData{$transactionDataKey}{$PLU};
                print $csvFile sprintf("%.2f,", $transactionData);
            }
        }

        # Ensure total values are neatly rounded to two decimal places
        elsif ($transactionDataKey =~ m/(Credit\sCards|Cash|Total\sTakings)/x) 
        {
            print $csvFile sprintf("%.2f,", $transactionData);
        }

        # Process other values
        elsif ($transactionDataKey ne "No Sale")
        {
            # Write comma separated values to the file
            print $csvFile "$transactionData,";
        }

        else
        {
            # Do not leave a trailing comma on the last value
            print $csvFile "$transactionData\n";
        }
    }

    $lastCalledHour = $currentEventHour; # Update last called hour, provides another layer of protection against duplicates

    return;
}

# This function normalises a string (removes non alphanumeric characters and converts to lowercase)
# It is used to compare shop names with the current hostname to assign an ID to the output file(s)
sub normaliseStr
{
    my ($rawString) = @_;

    # Remove blank spaces and the "SAMPi" prefix
    $rawString =~ s/[^\w]//gx;
    $rawString =~ s/SAMPi//igx;

    # Return lowercase representation
    return lc($rawString);
}

# This function normalises serial data by removing values which should not be seen by the parser
# It also makes certain additions and formatting fixes before passing thw data to the parser
# As the only data available from the 520 is the POLL output, greater normalisation is required
sub normaliseData
{
    my ($dataChunk) = @_;

    # 420 Normalisation
    unless ($SAM4S_520)
    {
        # Remove hexadecimal non-printing characters, question marks, etc.
        $dataChunk =~ s/\x{00}//gx; # Remove ASCII nulls
        $dataChunk =~ s/\x{c2}//gx; # Remove control characters
        $dataChunk =~ s/\x{9c}/$CURRENCY_SYMBOL/gx; # Replace unicode character with currency symbol
        $dataChunk =~s/\?/$CURRENCY_SYMBOL/gx; # As above for question marks
    }

    # 520 Normalisation
    else
    {
        $dataChunk =~ s/\@//gx; # Remove literal '@' symbols from data
        $dataChunk =~ s/\s[0-9]\s//gx; # Remove quantity specifiers (may be required in future)
        $dataChunk =~ s/(\d{1,2}.\d{2})/$CURRENCY_SYMBOL$1/gx; # Prepend currency symbol to values

        # Handle the fact that cash and change values appear on one line and the parser is line-based 
        # Detect the CASH chunk (which also contains the change
        if (index($dataChunk, "CASH") != -1)
        {
            my @sale = split('(CHANGE)', $dataChunk); # Split the chunk and keep the (delimiter)
            $sale[1] = $sale[1] . $sale[2]; # Combine the contents of the latter two indices, this is the 'CHANGE' identifier and the value

            $dataChunk = $sale[0]; # This sets $dataChunk to the normalised CASH / CARD identifier and value, process this first

            push(@dataBuffer, $sale[1]); # Push the change value into the databuffer, will be processed on next clear
        }
    }

    return $dataChunk;
}

# This function reads in the "shops.csv" file in the config subdirectory and assigns an ID based on
# The closest match between the current hostname and a shop name in the file. This is used to correctly
# name CSV output files without IDs being listed here in the source
sub getOutputFileName
{
    # Get the hostname and the filepath of the shops file
    my $currentHostname = hostname();
    my $shopFilePath = "config/shops.csv";

    # File handles for the shops file
    my $shopIDFile;

    # Undef if not matched
    my $matchedID = undef;
    my $numberInHostname = undef;

    # Get the current date for use in the filename
    my @currentDate = getCurrentDate();

    # Open the shops file in read mode
    ## no critic qw(RequireBriefOpen)
    unless (open ($shopIDFile, '<', "config/shops.csv"))
    {
        logMsg("Error opening $shopFilePath: $!");
        die "Error opening $shopFilePath: $!";
    }

    # Iterate through shops and shop IDs
    while (my $row = <$shopIDFile>)
    {
        chomp($row); # Remove blank lines

        (my $shopID, my $shopName) = split(',', $row, 2);

        # Normalise the strings for comparison
        $shopName        = normaliseStr($shopName);
        $currentHostname = normaliseStr($currentHostname);

        # Check for a number in the hostname
        if ($currentHostname =~ m/(\d)/g)
        {
            # Store the result
            $numberInHostname = $1;

            # Remove the number from the hostname for now so shop ID matching works
            $currentHostname =~ s/\d//gx;
        }
    
        # Check if normalised hostname exactly matches normalised shop name
        if ($currentHostname =~ /^$shopName$/x)
        {
            $matchedID = $shopID;
            last;
        }
    }

    close $shopIDFile;

    # If we couldn't find a match, set $matchedID to "UNKNOWN" and log a warning
    unless ($matchedID)
    {
        $matchedID = "UNKNOWN";
        logMsg("No match found for '$currentHostname' in shops.csv, setting \$matchedID to 'UNKNOWN'");
    }

    # Otherwise, check if this is a store with multiple ECR units and append to the filename to avoid conflicts if so
    if ($matchedID ne "UNKNOWN" && $numberInHostname)
    {
        # This relies on the hostname having a number appended to it and no single-till stores having numbers in their hostname
        $matchedID .= "_$numberInHostname";
    }

    # Set the filename in the format "yyyymmdd_$matchedID.csv"
    my $outputFileName = dirname($CURRENT_VERSION_PATH) . $DIRECTORY_SEPARATOR . "ecr_data" . $DIRECTORY_SEPARATOR .
       $currentDate[0] . $currentDate[1] . $currentDate[2] . "_$matchedID.csv";

    return $outputFileName;
}

# This function creates a CSV file in the local ecr_data directory with a list of predefined headings
# These files are named with the date the data was gathered and shop ID of where it was gathered
sub initialiseOutputFile
{
    my @csvHeadings; # Array of CSV headings
    my $outputFilePath = getOutputFileName(); 
    my $pluFile; # PLU filehandle

    # If the file does not exist, create it and add the correct headings
    unless (-e $outputFilePath)
    {
        logMsg("Creating CSV file $outputFilePath");

        ## no critic qw(RequireBriefOpen)
        unless (open ($csvFile, '>>', $outputFilePath))
        {
            logMsg("Error creating CSV output file at $outputFilePath");
            die("Error crearing CSV output file at $outputFilePath\n");
        }

        $csvOpen = TRUE;

        # Define the headings for the output file, these match the keys defined in the hourlyTransactionData hash
        foreach my $key (keys %hourlyTransactionData)
        {
            # PLU heading names are listed in the nested $PLUList hash
            if ($key eq "PLU")
            {
                foreach my $PLU (keys %PLUList)
                {
                    # Extract them and push them on to our array
                    push(@csvHeadings, $PLU);
                }
            }

            # Other headings are not nested
            else
            {
                push(@csvHeadings, $key); 
            }
        }

        # Write the headings to the CSV output file
        for my $currentHeading (0..$#csvHeadings) 
        {
            # Last header will end with a newline, others with a comma
            my $endChar = ($currentHeading == $#csvHeadings) ? "\n" : ",";

            print $csvFile $csvHeadings[$currentHeading] . $endChar;
        }
    }

    # If the file already exists, simply open it in append mode
    else
    {
        logMsg("Opening existing CSV file $outputFilePath");

        ## no critic qw(RequireBriefOpen)
        unless (open ($csvFile, '>>', $outputFilePath))
        {
            logMsg("Error opening CSV output file at $outputFilePath");
            die("Error opening CSV output file at $outputFilePath\n");
        }

        $csvOpen = TRUE;
    }

    $csvFile->autoflush(1); # Disable output buffering

    return;
}

# This function reads serial data from the ECR using the connection established by initialiseSerialPort()
# when running during business hours. It uses the parsedLineToCSV() function to collect sets of data and store it
# in CSV format for upload. If called outside of business hours it will periodically check for a new version of SAMPi.pl
sub processData
{
    my ($serialPort) = @_; # Get serial port file descriptor passed in

    # Ensure serial port object is available and valid
    unless ($serialPort && $serialPort->isa("Device::SerialPort"))
    {
        croak("Serial port has not been configured or is not open, call initialiseSerialPort() before this function\n");
    }

    my $firstRun = TRUE; # Flag which determines if this is the first time we are gong through the main loop

    my $pluFile; # File handle for the file containing valid PLU names

    # Read the plu.txt file in the config subdirectory to retrieve a list of acceptable PLU values
    unless (open ($pluFile, '<', "config/plu.txt"))
    {
        logMsg("Error reading PLU file, \"plu.txt\" should be in the config directory");
        die "Error reading PLU file\n";
    }

    # Populate the PLUList structure with the acceptable PLU values
    while (my $pluLine = <$pluFile>)
    {
        chomp $pluLine;
        next if ($pluLine =~ /^\s+$/x); # Ignore blank lines
        $PLUList{$pluLine} = "0"; # Initialise the nested hash
    }

    close ($pluFile);

    # Check to see if SAMPi is running during business hours which will determine if we are in active or idle mode 
    my $storeIsOpen = isBusinessHours();

    # Main loop
    while (TRUE)
    {
        # Read ECR data over serial and process it during business hours
        while ($storeIsOpen)
        {   
            # Load serialised data if we are recovering from a power failure or crash within the same hour
            # that the data was originally saved in.
            if ($firstRun)
            {
                my $currentHour = getCurrentHour();

                if (-e "hourlyData_$currentHour.dat")
                {
                    logMsg("Loading partial hourly transaction data for $currentHour:00 to " . ($currentHour+1) . ":00");
                    %hourlyTransactionData = %{ retrieve("hourlyData_$currentHour.dat") };        
                    unlink "hourlyData_$currentHour.dat";
                }

                $firstRun = FALSE;
            }

            # If we are not in debug mode we check the system clock as well as the header time in parseHeader() to
            # determine when to call the function to save the hourly data. This ensures new data is saved every hour 
            # regardless of input. We check to make sure we do not save mid-transaction so the data is not fragmented
            unless ($DEBUG_ENABLED)
            {
                # Get current UNIX time so we can compare with the time of the last transaction
                my $currentTime = time();

                # Last hour to compare with the lastSaved hour and prevent saving twice in one hour
                my $currentHour = getCurrentHour();

                # Ensure that the current system clock hour is different to the last saved time, we are not in the midst of a transaction and
                # that the last transaction was detected more than a configurable amount of time ago - implying that no new data is coming
                # for the previous hour as it was the last of the day
                if ( ($currentTime - $prevTransactionTime) > $TRANSACTION_DELAY_SECONDS && $currentHour > $lastSavedHour && $currentEvent != $PARSER_EVENTS{TRANSACTION})
                {
                    # Prevent saving on startup or when we have no new transactions to save
                    unless ($prevTransactionTime == 0 || $hourlyTransactionData{"Total Takings"} eq "0")
                    {
                        saveData();
                    }
                }
            }

            # Wait until we have read a line of data 
            if (my $serialDataChunk = $serialPort->lookfor()) 
            {
                # If we are in monitor mode
                if ($MONITOR_MODE_ENABLED)
                {
                    # Save the raw data to the log file
                    storeLine("$serialDataChunk\n");
                    next; # Do not parse the data
                }

                # Store the data if data logging is enabled
                if ($STORE_DATA_ENABLED)
                {
                    storeLine("$serialDataChunk\n");
                }

                # Sometimes data needs to be stored in a buffer for later processing (the 520 requires this to process cash and change)
                if (@dataBuffer)
                {
                    parseChunk(shift @dataBuffer); # Parse whatever is in the data buffer
                }

                # Parse the most recently received chunk of data
                parseChunk($serialDataChunk);
            }
            
            $storeIsOpen = isBusinessHours(); # Test if we are still running during opening hours 

            # 200ms delay to save CPU cycles
            sleep(0.2);
        }
    
        # If we are out of business hours then stop reading serial data, prepare variables for a new day 
        # and wait until the store reopens, whilst periodically checking for an updated version of SAMPi
        while (!$storeIsOpen)
        {
            my $sleepTime = 0;
            
            my $updateAvailable = checkForUpdate();
            
            if (!$updateAvailable)
            {
                logMsg("No update found, will try again in $UPDATE_CHECK_DELAY_MINUTES minutes");

                # Sleep for the whole update delay but check once a minute if we have entered business hours
                while ($sleepTime < $UPDATE_CHECK_DELAY_MINUTES * 60) 
                {
                    sleep(60);
                    $sleepTime += 60;
                    $storeIsOpen = isBusinessHours();
                }
            }
        }
    }

    return;
}

# Main function, called at start of execution
sub main
{
    logMsg("SAMPi v$VERSION Initialising...");

    # Check for updates on startup
    unless ($DEBUG_ENABLED || $VERBOSE_PARSER_ENABLED)
    {
        checkForUpdate();
    }

    # Run the update hook function if one is specified 
    if ($UPDATE_HOOK_ENABLED)
    {
        postUpdate();
    }

    # Print warning if monitor mode is enabled
    if ($MONITOR_MODE_ENABLED)
    {
        logMsg("MONITOR MODE ENABLED, STORING DATA");
    }

    if ($SAM4S_520)
    {
        logMsg("SAMPi 520 Mode Enabled");
    }

    # Initialise port and start processing data
    my $serialPort = initialiseSerialPort();
    processData($serialPort);
}

main();

__END__ # Required for Sys::RunAlone

