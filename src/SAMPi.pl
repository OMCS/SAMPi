#!/usr/bin/env perl
#
# SAMPi - SAM4S ECR data reader, parser and logger (Last Modified 04/10/2015)
#
# This software runs in the background on a suitably configured Raspberry Pi,
# reads from a connected SAM4S ECR via serial connection, extracts various data,
# puts it into CSV format and stores it in preparation for upload via SFTP
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

use constant::boolean; # Defines TRUE and FALSE values as Perl lacks an explicit boolean type
use Readonly; # Allows read-only constants
use Carp; # Provides alternative warn and die functions

use Sys::RunAlone; # This module ensures only one instance of this software runs concurrently
use Sys::Hostname; # Acquire hostname 
use Device::SerialPort; # Serial IO library 
use LWP::Simple qw(getstore is_error $ua); # Used to download updates
use Digest::SHA1 qw(sha1_base64); # SHA1 checksum library
use Time::HiRes qw(sleep); # Allows sleeping for less than a second
use Tie::IxHash; # Preserve insertion order on hash
use Text::Trim; # Remove leading and trailing whitespace

use File::Spec qw(tmpdir updir); # Used to get portable directory paths
use File::Compare; # Compare currently running script and downloaded script
use File::Touch; # Perl implementation of the UNIX 'touch' command
use File::Copy; # Provides the copy function
use File::Basename; # Get directory of currently executing script
use Scalar::Util qw(openhandle); # Test if file handle is open
use Cwd qw(abs_path); # Get absolute path of currently executing script

# Globally accessible constants and variables #

Readonly our $VERSION => 0.7;
Readonly my $LOGGING_ENABLED => TRUE; # Enable or disable logging to file
Readonly my $UPDATE_HOOK_ENABLED => FALSE; # Attempt to call the postUpdate() function once on start if TRUE
Readonly my $DEBUG_ENABLED => FALSE; # If enabled, the parser will print information as it runs

Readonly my $DIRECTORY_SEPARATOR => ($^O=~/Win/) ? "\\" : "/"; # Ternary operator used for brevity
Readonly my $CURRENT_VERSION_PATH => abs_path($0);
Readonly my $LATEST_VERSION_PATH => File::Spec->tmpdir() . $DIRECTORY_SEPARATOR . "SAMPi.pl";
Readonly my $UPDATE_CHECK_DELAY_MINUTES => 20; # Check for updates every 20 minutes in idle mode

# Define opening and closing hours
Readonly my $STORE_OPENING_HOUR_24 => 6;
Readonly my $STORE_CLOSING_HOUR_24 => 23;

# Constants used to identify which part of the data we are currently parsing
Readonly my %PARSER_EVENTS =>
(
    UNKNOWN     => -1,
    HEADER      =>  0,
    TRANSACTION =>  1,
    REPORT      =>  2
);

# File IO 
my $logOpen = 0; # Flag to determine if log file has been opened
my $logFile; # Log file descriptor, used in multiple functions
my $csvFile; # CSV file descriptor, used for output
my $serialPort; # Serial port file descriptor, used for input

# Updates and Idle Mode
my $updateAvailable = 0; # Update flag
my $postUpdateExecuted; # Filename referred to in postUpdate()
my $idleMode = FALSE; # Flag which tests if we have entered idle mode

# Parser State Variables
my $previousEvent = $PARSER_EVENTS{UNKNOWN}; # Track the previous event, used for counting transactions
my $previousEventTime = "0"; # Stores the time of the previous event (in  a string)
my $currentEvent = $PARSER_EVENTS{UNKNOWN}; # Tracks the current type of data being parsed
my $currentEventTime = "0"; # Store the time of the current event (in a string)
my $transactionCount = 1; # Counter for number of transactions per hour / day

# This data structure holds data for each of the columns which will eventually comprise the CSV file
# We store transactions as we read them, make calculations from this data and convert it to CSV hourly
my %hourlyTransactionData;

# Tie this hash to preserve insertion order for use as CSV column headings
tie %hourlyTransactionData, "Tie::IxHash";

# Initial values are set to zero
%hourlyTransactionData =
(
    "Hours"             => "0",
    "Total Takings"     => "0",
    "Cash"              => "0",
    "Credit Cards"      => "0",
    "Hot Food"          => "0",
    "Cold Takeaway"     => "0",
    "Meal Deal"         => "0",
    "Drinks"            => "0",
    "Crisps"            => "0",
    "Bread & Rolls"     => "0",
    "Cakes"             => "0",
    "Celebration Cake"  => "0",
    "Party Platters"    => "0",
    "Customer Count"    => "0",
    "First Transaction" => "0",
    "Last Transaction"  => "0"
);

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
    Readonly my $SERIAL_PORT => ($^O=~/Linux/) ? "/dev/ttyUSB0" : "/dev/ttys005"; # This varies depending on current OS
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
            }

            clearData(); # Clear the stored data
            $transactionCount = 1; # Reset the daily transaction count
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

    else
    {
        $previousEvent = $PARSER_EVENTS{UNKNOWN};
    }

    # Extract the event time into the $1 reserved variable
    $headerLine =~ /([0-9][0-9]:[0-9][0-9])/x;

    # Check that the extraction succeeded 
    if ($1)
    {
        # Keep track of the previous event time if there is one, ignoring reports
        if ($currentEventTime ne "0" and $currentEvent != $PARSER_EVENTS{REPORT})
        {
            # Used to set the last transaction time per hour
            $previousEventTime = $currentEventTime;
        }

        $currentEventTime = $1;
        my $currentEventHour = substr($currentEventTime, 0, 2);

        # When we have finished gathering data for the hour, we need to take it and write it out to the CSV file

        # If the current hour is different to the hour of the most recent transaction and this is not the beginning of the day
        if ($currentEventHour ne substr($hourlyTransactionData{"Hours"}, 0, 2) and $currentEvent != $PARSER_EVENTS{UNKNOWN})
        {
            # Set the last transaction time
            $hourlyTransactionData{"Last Transaction"} = $previousEventTime;

            # Write the collected data to the CSV file and clear the data structure
            logMsg("Generating CSV for " . $hourlyTransactionData{"Hours"});
            generateCSV();
            clearData();
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

    $currentEvent = $PARSER_EVENTS{HEADER};

    if ($DEBUG_ENABLED)
    {
        print "HEADER AT $currentEventTime\n";
    }

    return;
}

# This function is part of the parser, it processes transactions
# Each transaction is part of a group and contains the PLU and price for one or more 
# items. These are processed as key-value pairs with consideration for lines that
# do not represent PLUs (e.g. totals or payment method listings)
sub parseTransaction
{
    my ($transactionLine) = @_;

    $currentEvent = $PARSER_EVENTS{TRANSACTION};

    # Separate the data into a key (PLU) and a value (price) to use as input for the second-stage parser
    my ($transactionKey, $transactionValue) = split('£', $transactionLine, 2);

    # Treat the "TOTAL" line differently to a standard transaction line
    if (index($transactionKey, "TOTAL") != -1)
    {
        # Add to the hourly total 
        $hourlyTransactionData{"Total Takings"} += $transactionValue;
        return;
    }

    # Same for the 'CASH' line
    elsif (index($transactionKey, "CASH") != -1)
    {
        # Add to the hourly total for cash payments
        $hourlyTransactionData{"Cash"} += $transactionValue;
        return;
    }

    else
    {
        if ($DEBUG_ENABLED)
        {
            print "\tITEM FOR TRANSACTION $transactionCount\n";
        }

        # For regular transactions, add to the total for that type of product
        rtrim($transactionKey); # Remove any trailing spaces
        $hourlyTransactionData{$transactionKey} += $transactionValue; # Add to the appropriate column in the data

        return;
    }
}

# This function is responsible for parsing a line of serial data and storing various information which is later converted to CSV
sub parseLine
{
    # The line of data passed in as a parameter will be accessible as $dataLine
    my ($dataLine) = @_;

    # Replace any 0x9c hex values returned by the serial port with a GBP currency symbol
    $dataLine =~ s/\x{9c}/£/gx;

    # If the line begins with a date in dd/mm/yyyy format, it is a header
    if ($dataLine =~ /^[0-9][0-9]\/[0-9][0-9]\/[0-9][0-9][0-9][0-9]/x)
    {
        parseHeader($dataLine); # This will set $currentEvent to $HEADER
        return;
    }

    # Process the first line after a header
    if ($currentEvent == $PARSER_EVENTS{HEADER})
    {
        # Increment number of transactions if we have just processed one
        if ($previousEvent == $PARSER_EVENTS{TRANSACTION})
        {
            $transactionCount++;
            $hourlyTransactionData{"Customer Count"} = $transactionCount;
        }

        # If the line contains a price we are parsing a transaction
        if (index($dataLine, '£') != -1)
        {
            (my $PLU, undef) = split ('£', $dataLine, 2); # Extract the PLU

            trim($PLU); # Remove leading and trailing spaces

            # Ensure the PLU / key matches one of the expected categories
            if (exists ($hourlyTransactionData{$PLU}))
            {
                parseTransaction($dataLine);
            }

            else
            {
                logMsg("$PLU not recognised, not storing\n");
            }

            return;
        }

        # If the line matches a report, ignore it until the next header
        # We are currently ignoring reports in favour of collecting
        # data from individual transactions, this may change in future
        if (index($dataLine, 'REPORT') != -1)
        {
            $previousEvent = $PARSER_EVENTS{UNKNOWN};
            $currentEvent  = $PARSER_EVENTS{REPORT};
            return;
        }
    }

    # Ensure the line we are operating on matches a transaction
    elsif ($currentEvent == $PARSER_EVENTS{TRANSACTION} and index($dataLine, '£') != -1)
    {
        parseTransaction($dataLine);
        return;
    }
}

# This function resets the hourlyTransactionData hash to ready it for another hour of data
sub clearData
{
    # Iterate over the hash
    foreach my $key (keys %hourlyTransactionData)
    {
        # Reset each value
        $hourlyTransactionData{$key} = "0";
    }

    # Reset the hourly transaction count
    $transactionCount = 0;

    # Reset the stored event
    $previousEvent = $PARSER_EVENTS{UNKNOWN};

    return;
}

# This function writes the stored data to CSV format for uploading 
## no critic qw(RequireArgUnpacking)
sub generateCSV
{
    # Create an appropriately named CSV file and open it in append mode if it does not already exist
    if (!$csvFile)
    {
        initialiseOutputFile();
    }

    # Calculate amount spent on cards (TOTAL - CASH)
    $hourlyTransactionData{"Credit Cards"} = 
        $hourlyTransactionData{"Total Takings"} -
        $hourlyTransactionData{"Cash"};

    # Iterate through the hourly transaction data
    while (my ($transactionKey, $transactionData) = each %hourlyTransactionData)
    {
        if ($transactionKey ne "Last Transaction")
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

        if ($currentHostname =~ /$shopName/x)
        {
             $matchedID = $shopID;
        }
    }

    close $shopIDFile;

    # If we couldn't find a match, set $matchedID to "UNKNOWN" and log a warning
    if (!$matchedID)
    {
        $matchedID = "UNKNOWN";
        logMsg("No match found for '$currentHostname' in shops.csv, setting \$matchedID to 'UNKNOWN'");
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
        open($csvFile, '>>', $outputFilePath) or die "Error opening CSV file: $!";

        # Define the headings for the output file, these match the keys defined in the hourlyTransactionData hash
        foreach my $key (keys %hourlyTransactionData)
        {
            push(@csvHeadings, $key); # First argument is array, second is value to push
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
        open($csvFile, '>>', $outputFilePath) or die "Error opening CSV file: $!";
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

