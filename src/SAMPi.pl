#!/usr/bin/env perl
#
# SAMPi - SAM4S ECR data reader, parser and logger (Last Modified 09/10/2015)
#
# This software runs in the background on a suitably configured Raspberry Pi,
# reads from a connected SAM4S ECR via serial connection, extracts various data,
# puts it into CSV format and stores it in preparation for upload via (s)rysnc
#
# This software works in conjunction with the SAMPiD daemon to
# handle uploading CSV data files, removal of data older than 
# a configurable threshold and other miscellaneous tasks
#
# SAMPi.pl can be automatically updated by uploading a newer version
# to a configurable update URL

# Modern Perl #

use strict; 
use warnings;

# Imported Modules #

# Meta
use constant::boolean; # Defines TRUE and FALSE constants, Perl lacks an explicit boolean type
use Readonly; # Allows read-only constants
use Carp; # Provides alternative warn and die functions
use Data::Dumper; # Allows printing transaction data to screen for debugging

# Misc
use Sys::RunAlone; # This module ensures only one instance of this software runs concurrently
use Sys::Hostname; # Acquire hostname 
use Device::SerialPort; # Serial IO library 
use Tie::IxHash; # Preserve the insertion order of hashes
use Text::Trim; # Remove leading and trailing whitespace
use LWP::Simple qw(getstore is_error $ua); # Used to download updates
use Digest::SHA1 qw(sha1_base64); # SHA1 checksum library
use Time::HiRes qw(sleep); # Allows sleeping for less than a second
use Clone qw(clone); # Allows deep copying of nested hashes

# File I/O
use File::Spec qw(tmpdir updir); # Used to get portable directory paths
use File::Compare; # Compare currently running script and downloaded script
use File::Touch; # Perl implementation of the UNIX 'touch' command
use File::Copy; # Provides the copy function
use File::Basename; # Get directory of currently executing script
use Cwd qw(abs_path); # Get absolute path of currently executing script

# Globally accessible constants and variables TRUE

Readonly our $VERSION => 1.0;

Readonly my $LOGGING_ENABLED        => TRUE; # Enable or disable logging to file
Readonly my $UPDATE_HOOK_ENABLED    => FALSE; # Attempt to call the postUpdate() function once on start if TRUE
Readonly my $VERBOSE_PARSER_ENABLED => FALSE; # If enabled, the parser will print information as it runs
Readonly my $DEBUG_ENABLED          => TRUE; # If enabled, read current time from latest serial header instead of clock

Readonly my $DIRECTORY_SEPARATOR        => ($^O =~ /Win/) ? "\\" : "/"; # Ternary operator used for brevity
Readonly my $CURRENT_VERSION_PATH       => abs_path($0);
Readonly my $LATEST_VERSION_PATH        => File::Spec->tmpdir() . $DIRECTORY_SEPARATOR . "SAMPi.pl";
Readonly my $UPDATE_CHECK_DELAY_MINUTES => 20; # Check for updates every 20 minutes in idle mode

# Define opening and closing hours
Readonly my $STORE_OPENING_HOUR_24 => 6;
Readonly my $STORE_CLOSING_HOUR_24 => 23;

# Constants used to identify which part of the data we are currently parsing
Readonly my %PARSER_EVENTS =>
(
    HEADER      =>  0,
    TRANSACTION =>  1,
    OTHER       =>  2,
);

# File IO / Flags
my $logOpen = 0; # Flag to determine if log file has been opened
my $logFile; # Log file descriptor, used in multiple functions
my $csvOpen = 0; # Flag as above
my $csvFile; # CSV file descriptor, used for output
my $serialPort; # Serial port file descriptor, used for input
my $savedData = FALSE; # Indicates if we have saved data for the hour yet

# Updates and Idle Mode
my $updateAvailable = 0; # Update flag
my $postUpdateExecuted; # Filename referred to in postUpdate()
my $idleMode = FALSE; # Flag which tests if we have entered idle mode

# Parser State Variables
my $previousEvent = $PARSER_EVENTS{OTHER}; # Track the previous event, used for counting transactions
my $previousEventTime = "0"; # Stores the time of the previous event (in  a string)
my $currentEvent = $PARSER_EVENTS{OTHER}; # Tracks the current type of data being parsed
my $currentEventTime = "0"; # Store the time of the current event (in a string)
my $currentEventHour = "0"; # Just the hour portion of the current event time
my $transactionCount = 0; # Counter for number of transactions per hour / day

# The following hash is the list of recognised PLUs, in the future these could be read in from a file
# We tie this hash to preserve the insertion order for later use in CSV columns, saves front-end work
my %PLUList;
tie %PLUList, "Tie::IxHash";
%PLUList = 
(
    "Hot Food"         => "0",
    "Cold Takeaway"    => "0",
    "Meal Deal"        => "0",
    "Drinks & Crisps"  => "0",
    "Bread & Rolls"    => "0",
    "Cakes"            => "0",
    "Celebration Cake" => "0",
    "Party Platter"    => "0",
    "Carrier Bag"      => "0"
);

# The following data structure holds data for each of the columns that will eventually comprise the CSV file
# We store transactions as we read them, make calculations from this data and convert it to CSV once hourly
# This hash is tied for the same reason as the PLU list.
my %hourlyTransactionData;
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
my %hourlyTransactionDataCopy;
tie %hourlyTransactionDataCopy, "Tie::IxHash";

# Functions #

# Utility function which returns the current date in yyyymmdd as an array
sub getCurrentDate
{
    my @timestamp = localtime();
    
    my $currentYear  = $timestamp[5] + 1900; # Need to add 1900 to get the current year
    my $currentMonth = $timestamp[4] + 1; # Months from localtime() are zero-indexed
    my $currentDay   = $timestamp[3];

    if ($currentDay < 10)
    {
        $currentDay = "0" . $currentDay; # Pad day
    }

    my @currentDate = ($currentYear, $currentMonth, $currentDay);

    return @currentDate;
}

# Simple function to print logging messages  with a timestamp to a file and / or stdout 
sub logMsg
{
    # Take the message passed in as the first parameter and get the current time and date
    my $logMessage = shift;
    my $timestampStr = localtime();

    # Write message to file if logging is enabled
    if ($LOGGING_ENABLED)
    {
        if ($logOpen == 0)
        {
            # Create a new log file each month with the month and year included in the filename
            my @currentDate = getCurrentDate(); # Returned as year, month and day
            my $logFileName = "SAMPi-" . $currentDate[1] . "-" . $currentDate[0] . ".log"; # Construct the filename

            # Attempt to open the log file (located in the directory of the currently running script) in append mode
            ## no critic qw(RequireBriefOpen)
            if (open $logFile, '>>', dirname($0) . $DIRECTORY_SEPARATOR . $logFileName)
            {
                $logFile->autoflush(1); # Disable buffering
                $logOpen = 1;
            }

            # Print an error if unsuccessful 
            else
            {
                carp "Failed to open log file: $!\n";
                $logOpen = -1;
            }
        }

        if ($logOpen)
        {
            # Write message with timestamp to the log file
            print $logFile "$timestampStr: $logMessage\n";
        }
    }

    # Print the message to STDOUT in any case
    print "$timestampStr: $logMessage\n";

    return;
}

# This function initialises the serial port with the correct settings
# Modify this function if you require different settings 
sub initialiseSerialPort
{
    # 8N1 with software flow control by default
    Readonly my $SERIAL_PORT => ($^O =~ /Linux/i) ? "/dev/ttyUSB0" : "/dev/ttys004"; # This varies depending on current OS
    Readonly my $BPS => 9600;
    Readonly my $DATA_BITS => 8;
    Readonly my $STOP_BITS => 1;
    Readonly my $PARITY => "none";
    Readonly my $HANDSHAKE => "none";

    logMsg("Initialising Serial Port...");
    $serialPort = Device::SerialPort->new($SERIAL_PORT);

    # If there is an error initialising the serial port, print a warning and terminate
    if (!defined $serialPort)
    {
        logMsg("Error opening serial port $SERIAL_PORT: $!\n"); 
        die;
    }

    $serialPort->baudrate($BPS);
    $serialPort->databits($DATA_BITS);
    $serialPort->stopbits($STOP_BITS);
    $serialPort->parity($PARITY);
    $serialPort->handshake($HANDSHAKE);

    # Set lookfor() to match EOL characters so that we can read data line by line
    $serialPort->are_match( "\r", "\n" );
    $serialPort->lookclear;  

    logMsg("Opened serial port $SERIAL_PORT at $BPS" . "BPS");

    return;
}

# This utility function returns TRUE (provided by constant::boolean) if the current time is during business hours
# This will affect the behaviour of the script, it will either be in data gathering mode or idle / update mode
sub isBusinessHours
{
    my (undef, undef, $currentHour) = localtime();

    # Return true if we are within business hours
    if ($currentHour >= $STORE_OPENING_HOUR_24 and $currentHour <= $STORE_CLOSING_HOUR_24)
    {
        $idleMode = FALSE;
        return TRUE;
    }

    # Or false otherwise
    else
    {
        if (!$idleMode)
        {
            if (defined $csvFile)
            {
                close $csvFile; # Close the CSV file handle for the days' transactions
                $csvOpen = 0;
            }

            clearData(); # Clear the stored data
            $transactionCount = 0; # Reset the daily transaction count
            $idleMode = TRUE;
        }

        return FALSE;
    }
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
        return FALSE;
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
    if ($updateAvailable)
    {
        logMsg("Update found, overwriting $CURRENT_VERSION_PATH with $LATEST_VERSION_PATH");
        copy($LATEST_VERSION_PATH, $CURRENT_VERSION_PATH);
        logMsg("Restarting...");

        # Remove file which signifies we have run postUpdate() before if it exists
        if (-e $postUpdateExecuted)
        {
            unlink $postUpdateExecuted; 
        }

        exec $0; # Exec call replaces the currently running process with the new version
    }

    else
    {
        croak("This should not be called if there is no update available");
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

    if (!$postUpdateCode)
    {
        return;
    }

    # Generate checksum for requested postUpdate code, this prevents it running more than once
    my $checksum = sha1_base64($postUpdateCode);
    $checksum =~ s/$DIRECTORY_SEPARATOR/-/xg; # Replace anything matching the directory separator
    $postUpdateExecuted = dirname($CURRENT_VERSION_PATH) . $DIRECTORY_SEPARATOR . $checksum . ".run";

    if (not -f $postUpdateExecuted)
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

        touch $postUpdateExecuted;
    }

    else
    {
        logMsg("postUpdate() called previously, ignoring. Recommend setting \$UPDATE_HOOK_ENABLED to FALSE")
    }
    
    return;
}

# This function manages the saving of hourly data to persistent storage
# It sets the last transaction time, generates the CSV data
# and clears data structures 
sub saveData
{
    # Set the last transaction time
    $hourlyTransactionData{"Last Transaction"} = $previousEventTime;

    # Write the collected data to the CSV file and clear the data structure
    logMsg("Generating CSV for " . $hourlyTransactionData{"Hours"});
    generateCSV();
    clearData();

    $savedData = TRUE;

    return;
}

# This function is part of the parser, it processes headers
# Each header represents a separate event (transaction or report) and includes a 
# timestamp which is extracted and stored for later use
sub parseHeader
{
    my ($headerLine) = @_;
    
    # Keep track of the previous event if it was a transaction
    if ($currentEvent == $PARSER_EVENTS{TRANSACTION})
    {
        # This enables counting transactions
        $previousEvent = $PARSER_EVENTS{TRANSACTION};
    }

    $currentEvent = $PARSER_EVENTS{HEADER};

    # Extract the event time into the $1 reserved variable
    $headerLine =~ /([0-9][0-9]:[0-9][0-9])/x;

    # Check that the extraction succeeded 
    if ($1)
    {
        # Keep track of the previous event time if there is one, ignoring reports
        if ($currentEventTime ne "0" and $currentEvent != $PARSER_EVENTS{OTHER})
        {
            # Used to set the last transaction time for each hour
            $previousEventTime = $currentEventTime;
        }

        $currentEventTime = $1; 
        $currentEventHour = substr($currentEventTime, 0, 2);

        # When we have finished gathering data for the hour, we need to take it and write it out to the CSV file
        # If we are debugging, we use the hours in the serial headers to indicate the current hour 
        # so we don't have to wait until the actual hour changes to generate CSV data 
        if ($DEBUG_ENABLED)
        {
            # If the current hour is different to the hour of the most recent transaction and this is not the beginning of the day
            if ($currentEventHour ne substr($hourlyTransactionData{"Hours"}, 0, 2) and $hourlyTransactionData{"Hours"} ne "0")
            {
                saveData(); 
            }
        }

        # If no first transaction has been logged for the current hour
        if ($hourlyTransactionData{"First Transaction"} eq "0")
        {
            # Set the 'Hours' field accordingly, in the format "HH.00 - HH+1.00"
            my $nextHour = $currentEventHour+1;
            $hourlyTransactionData{"Hours"} = "$currentEventHour.00-$nextHour.00";

            # Store the time of the first transaction
            $hourlyTransactionData{"First Transaction"} = $currentEventTime;           
        }
    }

    # Update customer (transaction) count in the hourly data structure
    $hourlyTransactionData{"Customer Count"} = $transactionCount;

    if ($VERBOSE_PARSER_ENABLED)
    {
        print "HEADER AT $currentEventTime\n";
    }

    return;
}

# This function is part of the parser, it processes transactions
# Each transaction is part of a group and contains the PLU and price for one or more 
# items. These are processed as key-value pairs with consideration for lines that
# do not represent PLUs (e.g. totals or payment method listings)
## no critic qw(ProhibitCascadingIfElse)
sub parseTransaction
{
    my ($transactionLine) = @_;

    $currentEvent = $PARSER_EVENTS{TRANSACTION};

    # Separate the data into a key (PLU) and a value (price) to use as input for the second-stage parser
    my ($transactionKey, $transactionValue) = split('£', $transactionLine, 2);

    # If we read a 'TOTAL' line
    if (index($transactionKey, "TOTAL") != -1)
    {
        # Add to the hourly total 
        $hourlyTransactionData{"Total Takings"} += $transactionValue;

        # Increment the transaction total, can decrement later if we read a cancel
        # or a reprint
        $transactionCount++;
        return;
    }

    # Handle the 'CASH' total
    elsif (index($transactionKey, "CASH") != -1)
    {
        # Add to the hourly total for cash payments
        $hourlyTransactionData{"Cash"} += $transactionValue;
        return;
    }

    # Do not include money given back as change in the amount of cash taken in
    elsif (index($transactionKey, "CHANGE") != -1)
    {
        $hourlyTransactionData{"Cash"} = $hourlyTransactionData{"Cash"} - $transactionValue;
        return;
    }

    # Handle "CHEQUE" lines currently signifying card payments, also handle "CARD"
    elsif (index($transactionKey, "CHEQUE") != -1 or $transactionKey =~ /^CARD/x)
    {
        # Add to the hourly total for card payments
        $hourlyTransactionData{"Credit Cards"} += $transactionValue;
        return;
    }

    # Keep track of "NO SALE" lines, from people opening the till without processing a transaction
    elsif (index($transactionKey, "NOSALE") != -1)
    {
        logMsg("Till opened but no transaction processed at $currentEventTime");   
        $hourlyTransactionData{"No Sale"}++;
        return;
    }

    else
    {
        # For regular transactions, do some validation and then add 
        # to the total for that PLU / product category 
        
        trim($transactionKey); # Remove leading and trailing spaces
        $transactionKey =~ s/(\w+)/\u\L$1/gx; # Normalise PLU case to 'Title Case'

        # Ensure the PLU / key matches one of the expected categories
        if (exists($PLUList{$transactionKey}))
        {
            # Add to the appropriate column in the data
            $hourlyTransactionData{"PLU"}{$transactionKey} += $transactionValue; 
        }

        else
        {
            logMsg("\"$transactionKey\" is not a valid PLU, ignoring");
        }

        if ($VERBOSE_PARSER_ENABLED)
        {
            print "\tITEM FOR TRANSACTION $transactionCount\n";
        }

        return;
    }
}

# This function is responsible for parsing a line of serial data and storing various information which is later converted to CSV
sub parseLine
{
    # The line of data passed in as a parameter will be accessible as $dataLine
    my ($dataLine) = @_;

    # Replace any 0xc2 and 0x9c hex values, question marks or nulls returned by the serial port
    $dataLine =~ s/\x{c2}//gx;
    $dataLine =~ s/\x{9c}/£/gx;
    $dataLine =~s/\?/£/gx;
    $dataLine =~ s/\x{00}//gx;

    # Set previous event correctly for reports
    if ($currentEvent == $PARSER_EVENTS{OTHER})
    {
        $previousEvent = $PARSER_EVENTS{OTHER};
    }

    # If the line starts with a date in dd/mm/yyyy format, it is a header
    if ($dataLine =~ /^\d{1,2}\/\d{2}\/\d{4}/x)
    {
        parseHeader($dataLine); # This will set $currentEvent to $HEADER
        return;
    }

    # Handle cancelled and reprinted transactions
    elsif ( ($dataLine =~ /^CANCEL/x or $dataLine =~ /REPRINT/x) and $currentEvent != $PARSER_EVENTS{OTHER} )
    {
        # Reset the state of the hourly transaction data to how it was before the current transaction
        logMsg("Ignoring cancelled or reprinted transaction at $currentEventTime");
        %hourlyTransactionData = %hourlyTransactionDataCopy;
        $transactionCount--;
        $hourlyTransactionData{"Customer Count"} = $transactionCount;
        $currentEvent = $PARSER_EVENTS{OTHER};
        return;
    }

    # Ignore refunds for now, we aren't tracking them
    elsif ($dataLine =~/^PAID\sOUT/x and $currentEvent != $PARSER_EVENTS{OTHER})
    {
        logMsg("SAMPi does not currently implement refund tracking, ignoring");
        $currentEvent = $PARSER_EVENTS{OTHER};
        return;
    }

    # Ignore any settings or debugging information on the printout 
    elsif ($dataLine =~/=/x and $currentEvent != $PARSER_EVENTS{OTHER}) 
    {
        logMsg("Ignoring diagnostic output: $dataLine");
        $currentEvent = $PARSER_EVENTS{OTHER};
        return;
    }

    # Process the first line after a header
    if ($currentEvent == $PARSER_EVENTS{HEADER})
    {
        # Make a copy of the current transaction data so we can revert if requried
        %hourlyTransactionDataCopy = %{ clone(\%hourlyTransactionData) };

        # Print out the most recently processed transaction if we are debugging
        if ($previousEvent == $PARSER_EVENTS{TRANSACTION})
        {
            if ($VERBOSE_PARSER_ENABLED)
            {
                print Dumper(\%hourlyTransactionData);
            }
        }

        # If the line matches a report, ignore it until the next header
        # We are currently ignoring reports in favour of collecting
        # data from individual transactions, this may change in future
        if (index($dataLine, 'REPORT') != -1)
        {
            if ($VERBOSE_PARSER_ENABLED)
            {
                print "Ignoring report at $currentEventTime\n";
            }

            $currentEvent = $PARSER_EVENTS{OTHER};
        }

        # If the line isn't a report and contains a price, prepare to process a transaction
        if (index($dataLine, '£') != -1 and $currentEvent != $PARSER_EVENTS{OTHER})
        {
            $currentEvent = $PARSER_EVENTS{TRANSACTION};
        }
    }

    # Ensure the line we are operating on matches a transaction
    if ($currentEvent == $PARSER_EVENTS{TRANSACTION} and index($dataLine, '£') != -1)
    {
        parseTransaction($dataLine);
        return;
    }
}

# This function resets the hourlyTransactionData hash to ready it for another hour of data
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

    # Reset counts and flags
    $transactionCount = 0;
    $savedData = FALSE;

    return;
}

# This function writes the stored data to CSV format for uploading 
## no critic qw(RequireArgUnpacking)
sub generateCSV
{
    # Create an appropriately named CSV file and open it in append mode if it does not already exist
    if (!$csvOpen)
    {
        initialiseOutputFile();
    }

    # Sanity check, do not generate a row of CSV if there were no transactions
    if ($hourlyTransactionData{"Total Takings"} eq "0")
    {
        logMsg("No transactions read for " . $hourlyTransactionData{"Hours"} . ", discarding CSV"); 
        return;
    }

    $hourlyTransactionData{"Customer Count"} = $transactionCount;

    # Iterate through the hourly transaction data
    while (my ($transactionDataKey, $transactionData) = each %hourlyTransactionData)
    {
        # Process PLU totals
        if ($transactionDataKey eq "PLU")
        {
            # Iterate over the nested hash and extract the saved data
            foreach my $PLU (keys %{ $hourlyTransactionData{$transactionDataKey} })
            {
                $transactionData = $hourlyTransactionData{$transactionDataKey}{$PLU};
                print $csvFile "$transactionData,";
            }
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

    return;
}

# This function normalises a string (removes spaces and special characters and converts to lowercase)
# It is used to compare shop names with the current hostname to assign an ID to the output file(s)
sub normalise
{
    my ($rawString) = @_;

    $rawString =~ s/[^\w]//gx;

    return lc($rawString);
}

# This function reads in the "shops.csv" file in the current parent directory and assigns an ID based on
# The closest match between the current hostname and a shop name in the file, this is used to correctly
# name CSV output files without this being hardcoded in the source
sub getOutputFileName
{
    # Get the hostname and the filepath of the shops file
    my $currentHostname = hostname();
    my $shopFilePath = File::Spec->updir() . $DIRECTORY_SEPARATOR . "shops.csv";

    # File handles for the shops file
    my $shopIDFile;

    # Undef if not matched
    my $matchedID = undef;

    # Get the current date for use in the filename
    my @currentDate = getCurrentDate();

    # Open the shops file in read mode
    ## no critic qw(RequireBriefOpen)
    my $open = open($shopIDFile, "<", $shopFilePath);
    
    if (!$open)
    {
        logMsg("Error opening $shopFilePath: $!");
        die "Error opening $shopFilePath: $!";
    }

    # Iterate through
    while (my $row = <$shopIDFile>)
    {
        chomp($row);

        (my $shopID, my $shopName) = split(',', $row, 2);

        # Normalise the strings for comparison
        $shopName        = normalise($shopName);
        $currentHostname = normalise($currentHostname);

        # Check if the hostname contains the shop name
        if ($currentHostname =~ /$shopName/x)
        {
            $matchedID = $shopID;
        }
    }

    close $shopIDFile;

    # If we couldn't find a match, set $matchedID to "OTHER" and log a warning
    if (!$matchedID)
    {
        $matchedID = "UNKNOWN";
        logMsg("No match found for '$currentHostname' in shops.csv, setting \$matchedID to 'UNKNOWN'");
    }

    # Otherwise, check if this is a store with multiple ECR units and append to the filename to avoid conflicts if so
    elsif ($currentHostname =~ /([0-9])/x)
    {
        # This relies on the hostname having a number appended to it and no one-till stores having numbers in their hostname
        $matchedID .= "_$1";
    }

    # Set the filename in the format "yyyymmdd_matchedID.csv"
    my $outputFileName = dirname(dirname($CURRENT_VERSION_PATH)) . $DIRECTORY_SEPARATOR . "ecr_data" . $DIRECTORY_SEPARATOR .
        $currentDate[0] . $currentDate[1] . $currentDate[2] . "_$matchedID.csv";

    return $outputFileName;
}

# This function creates a CSV file in the local ecr_data directory with a list of predefined headings
# and named with the date of creation and hostname of the machine SAMPi is running on
sub initialiseOutputFile
{
    my @csvHeadings; # Store CSV headings
    my $outputFilePath = getOutputFileName(); 

    # If the file does not exist, create it and add the correct headings
    if (! -e $outputFilePath)
    {
        logMsg("Creating CSV file $outputFilePath");

        ## no critic qw(RequireBriefOpen)
        $csvOpen = open($csvFile, '>>', $outputFilePath) or die "Error opening CSV file: $!";

        # Define the headings for the output file, these match the keys defined in the hourlyTransactionData hash
        foreach my $key (keys %hourlyTransactionData)
        {
            # PLU column names are listed in the PLUList structure
            if ($key eq "PLU")
            {
                foreach my $PLU (keys %PLUList)
                {
                    # Extract them and push them on to our array
                    push(@csvHeadings, $PLU);
                }
            }

            else
            {
                push(@csvHeadings, $key); 
            }
        }

        # Write the headings to the file
        for my $i (0..$#csvHeadings) 
        {
            if ($i == $#csvHeadings)
            {
                print $csvFile "$csvHeadings[$i]\n"; # No comma
            }

            else
            {
                print $csvFile "$csvHeadings[$i],";
            }
        }
    }

    # If the file already exists, simply open it in append mode
    else
    {
        logMsg("Opening existing CSV file $outputFilePath");
        ## no critic qw(RequireBriefOpen)
        $csvOpen = open($csvFile, '>>', $outputFilePath) or die "Error opening CSV file: $!";
    }

    $csvFile->autoflush(1);

    return;
}

# This function reads serial data from the ECR using the connection established by initialiseSerialPort()
# when running during business hours. It uses the parsedLineToCSV() function to collect sets of data and store it
# in CSV format for upload. If called outside of business hours it will periodically check for updates
sub processData
{
    if (!$serialPort)
    {
        croak("Serial port has not been configured, call initialiseSerialPort() before this function");
    }

    # Check to see if SAMPi is running during business hours which will determine active / idle mode 
    my $storeIsOpen = isBusinessHours();

    # Main loop
    while (TRUE)
    {
        # Read ECR data over serial and process it during business hours
        while ($storeIsOpen)
        {
            # Wait until we have read a line of data 
            if (my $serialDataLine = $serialPort->lookfor()) 
            {
                # Parse the line of data
                parseLine($serialDataLine);
            }
            
            # If we are not in debug mode we will check the system clock 
            # rather than the time in the headers of the serial data
            # This ensures new data is saved every hour regardless of input
            if (!$DEBUG_ENABLED)
            {
                my (undef, undef, $currentHour) = localtime();

                if ($currentEventHour ne "0" and $currentEventHour ne $currentHour)
                {
                    if (!$savedData)
                    {
                        saveData();
                    }
                }
            }

            $storeIsOpen = isBusinessHours();

            # 200ms delay to save CPU cycles
            sleep(0.2);
        }
    
        # If we are out of business hours, stop reading serial data and wait until the store reopens, 
        # checking periodically for an updated version of this software
        while (!$storeIsOpen)
        {
            logMsg("Checking for updates every $UPDATE_CHECK_DELAY_MINUTES minutes");

            # Check if the current script and latest script on the server differ
            $updateAvailable = isUpdateAvailable();

            if ($updateAvailable)
            {
                # Install the newer version of the script and run it
                logMsg("New version is available, updating and restarting");
                updateAndReload();
            }

            else
            {
                logMsg("No update found, will try again later");
                sleep($UPDATE_CHECK_DELAY_MINUTES * 60); # The parameter must be in seconds
            }

            $storeIsOpen = isBusinessHours();
        }
    }

    return;
}

# Main function, called at start of execution
sub main
{
    logMsg("SAMPi v$VERSION Initialising...");

    if ($UPDATE_HOOK_ENABLED)
    {
        postUpdate();
    }

    initialiseSerialPort();
    processData();

    exit;
}

main();

__END__ # Required for Sys::RunAlone

