#!/usr/bin/env perl
#
# SAMPi - SAM4S ECR Reader, Parser and Logger (Last Modified 27/09/2015)
#
# This software runs as a daemon on a suitably configured Raspberry Pi,
# reads from a connected SAM4S ECR via RS232, extracts various data
# in CSV format and stores it in preparation for upload via SFTP or a 
# another suitable protocol using SAMPi_UPLOAD.sh

use strict; 
use warnings;
use Readonly;
use constant::boolean;

Readonly our $VERSION => 0.4;

# Logging
Readonly my $ENABLE_LOGGING => 1; # Enable or disable logging to file
my $logOpen = 0;
my $logFile;

# Serial Communications
use Device::SerialPort; 
my $serialPort;

# File handling
use File::HomeDir; # Access home directory in a portable way
use File::Spec; # Used to get portable temporary directory path
use File::Compare; # Compare old files and most recently updated file
use File::Copy; # Copy and move
use Cwd 'abs_path'; # Get absolute path of currently executing script

Readonly my $CURRENT_VERSION_PATH => abs_path($0);
Readonly my $LATEST_VERSION_PATH => File::Spec->tmpdir() . "/SAMPi.pl";
my $updateAvailable = 0;

# Networking
use LWP::Simple; # Download updates

# Simple function to print logging messages
# with a timestamp to a file and / or stdout 
sub logMsg
{
    # Take the message passed in as the first parameter and get the current time and date
    my $logMessage = shift;
    my @timestamp = localtime();
    my $timestampStr = localtime();

    # Write message to file if logging is enabled
    if ($ENABLE_LOGGING)
    {
        if ($logOpen == 0)
        {
            # Create a new log file each month with the month and year included in the filename
            my $currentMonth = $timestamp[4] + 1; # Months from localtime() are zero-indexed
            my $currentYear = $timestamp[5] + 1900; # Need to add 1900 to get the current year
            my $logFileName = "SAMPi-" . $currentMonth . "-" . $currentYear . ".log"; # Construct the filename

            # Attempt to open the log file in append mode
            ## no critic qw(RequireBriefOpen)
            if (open $logFile, '>>', $logFileName)
            {
                $logFile->autoflush(1); # Disable buffering
                $logOpen = 1;
            }

            # Print an error if unsuccessful 
            else
            {
                warn "Failed to open log file: $!\n";
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

# This function checks to see if a new version is available and returns the true if this is the case
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
        return "";
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
        exec $0; # Exec call replaces running script
    }

    else
    {
        croak("This should not be called if there is no update available");
    }

    return;
}

# This function reads serial data from the ECR using the connection established by initialiseSerialPort()
sub readSerialData
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
        # Check to see if SAMPi is running during business hours
        my $storeIsOpen = isBusinessHours();

        while ($storeIsOpen)
        {
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
        # checking periodically for an updated version (see SAMPi_UPDATE.sh for more info)
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
                # Check if we need to exit this subloop and delay for the user configurable number of seconds between update checks
                $storeIsOpen = isBusinessHours();
                sleep($UPDATE_CHECK_DELAY_MINUTES * 60);
            }
        }
    }

    return;
}

# Main function
sub main
{
    logMsg("SAMPi v$VERSION Initialising...");
    initialiseSerialPort();
    readSerialData();

    exit;
}

main();

