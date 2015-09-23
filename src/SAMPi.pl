#!/usr/bin/env perl
#
# SamPI - SAM4S ECR Reader and Parser (Last Modified 24/09/2015)
#
# This software runs as a daemon on a suitably configured Raspberry Pi,
# reads from a connected SAM4S ECR via RS232, extracts various data
# in CSV format and stores it in preparation for upload via SFTP or a 
# another suitable protocol using SAMPi_UPLOAD.sh

use strict; 
use warnings;

use constant VERSION => 0.1;

# Logging
use constant ENABLE_LOGGING => 1; # Enable or disable logging to file
my $logOpen = 0;
my $logFile;

# Serial Communications
use Device::SerialPort; # Serial port library we will be using
#use constant SERIAL_PORT => "/dev/ttyUSB0";
use constant SERIAL_PORT => "/dev/cu.Bluetooth-Incoming-Port";
use constant BPS => 9600;
my $serialPort;

# Simple function to print logging messages
# with a timestamp to a file and / or stdout 
sub logMsg
{
    # Take the message passed in as the first parameter and get the current time
    my $logMessage = shift;
    my $timestamp = localtime(time);

    # Write message to file if enabled
    if (ENABLE_LOGGING)
    {
        if ($logOpen == 0)
        {
            # Attempt to open the log file in append mode
            if (open $logFile, '>>', "SAMPi.log")
            {
                $| = 1; # Disable buffering
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
            # Write message with timestamp to STDOUT
            print $logFile "$timestamp: $logMessage\n";
        }
    }

    # Print the message to STDOUT in any case
    print "$timestamp: $logMessage\n";
}

# This function initialises the serial port with the correct settings
# Modify this function if you require different settings 
sub initialiseSerialPort
{
    logMsg("Initialising Serial Port...");
    $serialPort = Device::SerialPort->new(SERIAL_PORT);

    # If there is an error initialising the serial port, print a warning and terminate
    if (!defined $serialPort)
    {
        logMsg("Error opening serial port " . SERIAL_PORT . ": $!\n"); 
        die;
    }

    # 8N1 with software flow control
    $serialPort->baudrate(BPS);
    $serialPort->databits(8);
    $serialPort->stopbits(1);
    $serialPort->parity("none");
    $serialPort->handshake("xoff");

    logMsg("Opened serial port " . SERIAL_PORT . " at " . BPS . " BPS");
}

sub readSerialData
{
    while (1)
    {
        $serialPort->read_char_time(0);     # Don't wait for each character
        $serialPort->read_const_time(2000); # 2 seconds per unfulfilled "read" call
         
        # Read up to 255 characters, may need to be adjusted
        my ($count, $serialData) = $serialPort->read(255);
            
        if ($count > 0) 
        {
            # Print data received from ECR via serial
            print $serialData;
        }
    }
}

logMsg("SAMPi v" . VERSION . " Initialising...");
initialiseSerialPort();
readSerialData();

