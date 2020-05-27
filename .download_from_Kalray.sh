#!/bin/sh
mkdir download
cd download
sshpass "-p$KALRAY_SFTP_PASSWORD" sftp -o "StrictHostKeyChecking=no" compcert@ssh.kalray.eu <<EOF
cd files
get DEB.tar
EOF
tar xf DEB.tar
