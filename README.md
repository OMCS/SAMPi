# SAMPi
SAM4S ECR Reader, Parser &amp; Logger

This software runs in the background on a suitably configured Raspberry Pi. It reads from a connected SAM4S ECR via a serial connection; extracts various data, puts it into CSV format and stores it in preparation for upload via rysnc or SFTP.

This software works in conjunction with the SAMPiD daemon to handle uploading CSV data files, removal of data older than 
a configurable threshold and other miscellaneous tasks.

SAMPi.pl can be automatically updated by uploading a newer version to a configurable update URL.
