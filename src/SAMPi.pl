#!/usr/bin/env perl
#
# SAMPi - SAM4S ECR data reader, parser and logger (Last Modified 29/09/2015)
#
# This software runs in the background on a suitably configured Raspberry Pi,
# reads from a connected SAM4S ECR via serial connection, extracts various data,
# puts it into CSV format and stores it in preparation for upload via SFTP
#
# This software works in conjunction with the SAMPiD daemon to
# handle uploading csv data files, removal of data older than 
# a configurable threshold and handle other miscellaneous tasks
#
# SAMPi.pl can be automatically updated by uploading a newer version
# accessible using a configurable URL

# Modern Perl #

use strict; 
use warnings;

# Imported Modules #

use constant::boolean; # Defines TRUE and FALSE values as Perl lacks an explicit boolean type
use Readonly; # Allows read-only constants
use Carp; # Alternative warn and die functions

use Sys::RunAlone; # This module ensures only one instance of this software runs concurrently
use Device::SerialPort; # Serial IO library 
use LWP::Simple qw(getstore is_error); # Used to download updates
use Digest::SHA1 qw(sha1_base64); # SHA-1 checksum library

use File::Spec qw(tmpdir); # Used to get portable temporary directory path
use File::Compare; # Compare currently running script and downloaded script
use File::Touch; # Perl implementation of the UNIX 'touch' command
use File::Copy; # Provides the copy function
use File::Basename; # Get directory of currently executing script
use Cwd qw(abs_path); # Get absolute path of currently executing script

# Globally accessible constants and variables #

Readonly our $VERSION => 0.4;
Readonly my $LOGGING_ENABLED => TRUE; # Enable or disable logging to file
Readonly my $UPDATE_HOOK_ENABLED => FALSE; # Attempt to call the postUpdate() function once on start if TRUE

Readonly my $DIRECTORY_SEPARATOR => ($^O=~/Win/) ? "\\" : "/"; # Ternary operator used for brevity
Readonly my $CURRENT_VERSION_PATH => abs_path($0);
Readonly my $LATEST_VERSION_PATH => File::Spec->tmpdir() . $DIRECTORY_SEPARATOR . "SAMPi.pl";

my $logOpen = 0; # Flag to determine if log file has been opened
my $logFile; # Log file descriptor, used in multiple functions
my $serialPort; # Serial port file descriptor, as above
my $updateAvailable = 0; # Update flag
my $postUpdateExecuted; # Filename referred to in postUpdate()

# Functions #

# Simple function to print logging messages  with a timestamp to a file and / or stdout 
sub logMsg
{
    # Take the message passed in as the first parameter and get the current time and date
    my $logMessage = shift;
    my @timestamp = localtime();
    my $timestampStr = localtime();

    # Write message to file if logging is enabled
    if ($LOGGING_ENABLED)
    {
        if ($logOpen == 0)
        {
            # Create a new log file each month with the month and year included in the filename
            my $currentMonth = $timestamp[4] + 1; # Months from localtime() are zero-indexed
            my $currentYear = $timestamp[5] + 1900; # Need to add 1900 to get the current year
            my $logFileName = "SAMPi-" . $currentMonth . "-" . $currentYear . ".log"; # Construct the filename

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
    Readonly my $SERIAL_PORT => "/dev/ttyUSB0";
    Readonly my $BPS => 9600;
    Readonly my $DATA_BITS => 8;
    Readonly my $STOP_BITS => 1;
    Readonly my $PARITY => "none";
    Readonly my $HANDSHAKE => "xoff";

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

    logMsg("Opened serial port $SERIAL_PORT at $BPS" . "BPS");

    return;
}

# This utility function returns TRUE (provided by constant::boolean) if the current time is during business hours
# This will affect the behaviour of the script, it will either be in data gathering mode or idle / update mode
sub isBusinessHours
{
    Readonly my $STORE_OPENING_HOUR_24 => 9;
    Readonly my $STORE_CLOSING_HOUR_24 => 17;

    my @currentTime = localtime();
    my $currentHour = $currentTime[2];

    # Return true if we are within business hours
    if ($currentHour >= $STORE_OPENING_HOUR_24 and $currentHour <= $STORE_CLOSING_HOUR_24)
    {
        return TRUE;
    }

    # Or false otherwise
    else
    {
        return FALSE;
    }
}

# This function checks to see if a new version is available and returns true if this is the case
sub isUpdateAvailable
{   
    Readonly my $UPDATE_URL => "https://dl.dropboxusercontent.com/u/12186225/SAMPi.pl";

    logMsg("Checking for update...");
    logMsg("Attempting to download from update URL... ($UPDATE_URL)");

    # Save the latest available version in a temporary directory
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
    if ($updateAvailable)
    {
        logMsg("Update found, overwriting $CURRENT_VERSION_PATH with $LATEST_VERSION_PATH");
        copy($LATEST_VERSION_PATH, $CURRENT_VERSION_PATH);
        logMsg("Restarting...");
        unlink $postUpdateExecuted; # Remove file which signifies we have run postUpdate() before
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
        ## no critic (ProhibitStringyEval)
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

# This function reads serial data from the ECR using the connection established by initialiseSerialPort()
# when running during business hours. It uses the dataToCSV() function to collect sets of data and store it
# in CSV format for upload. If called outside of business hours it will periodically check for updates
sub processData
{
    if (!$serialPort)
    {
        croak("Serial port has not been configured, call initialiseSerialPort() before this function");
    }

    Readonly my $DATA_SIZE_BYTES => 256;
    Readonly my $READ_DELAY_SECONDS => 2000;

    # Main loop
    while (1)
    {
        # Check to see if SAMPi is running during business hours and enter the appropriate loop
        my $storeIsOpen = isBusinessHours();

        # Read ECR data over serial and process it during business hours
        while ($storeIsOpen)
        {
            # Set parameters for serial I/O
            $serialPort->read_char_time(0); # Read characters as they are received
            $serialPort->read_const_time($READ_DELAY_SECONDS); # Time to wait between read calls 
         
            # Read a number of characters from the serial port
            my ($bytesReceived, $serialData) = $serialPort->read($DATA_SIZE_BYTES);
            
            if ($bytesReceived > 0)
            {
                # Print data received from ECR via serial
                print $serialData;
            }

            else
            {
                printf "%s seconds passed\n", $READ_DELAY_SECONDS / 1000;
            }

            # Update current hour
            $storeIsOpen = isBusinessHours();
        }
    
        # If we are out of business hours, stop reading serial data and wait until the store reopens, 
        # checking periodically for an updated version of this software
        while (!$storeIsOpen)
        {
            # Set delay for checking if an update is available
            Readonly my $UPDATE_CHECK_DELAY_MINUTES => 20; 

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

                # Check if we need to exit this subloop and delay for the (user-configurable) number of seconds between update checks
                $storeIsOpen = isBusinessHours();

                if ($storeIsOpen)
                {
                    last;
                }

                sleep($UPDATE_CHECK_DELAY_MINUTES * 60);
            }
        }
    }

    return;
}

# This function takes data gathered over the serial connection by the processData() function
# Parses the required fields and converts them into CSV formated files suitable for uploading
sub dataToCSV
{
    # TODO: Implement this function
    
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

