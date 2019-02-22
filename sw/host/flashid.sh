#!bin/bash

./wbregs flashcfg 0x0001100	# Activate config mode
./wbregs flashcfg 0x00010ff	# Send 16(*2) bits of ones, break the mode
./wbregs flashcfg 0x00010ff
./wbregs flashcfg 0x00010ff
./wbregs flashcfg 0x00010ff
./wbregs flashcfg 0x0001100	# Inactivate the port

# Reset the SCOPE
./wbregs flashscope 0x07ffff
# echo READ-ID
./wbregs flashcfg 0x000109f	# Issue the read ID command
./wbregs flashcfg 0x0001000	# Read the ID
./wbregs flashcfg
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	# End the command

echo Status register
./wbregs flashcfg 0x0001005	# Read status register
./wbregs flashcfg 0x0001000	#
./wbregs flashcfg
./wbregs flashcfg 0x0001100	#

echo Return to QSPI
./wbregs flashcfg 0x00010bb	# Return us to QSPI mode, via QIO_READ cmd
./wbregs flashcfg 0x0001a00	# dummy address
./wbregs flashcfg 0x0001a00	# dummy address
./wbregs flashcfg 0x0001a00	# dummy address
./wbregs flashcfg 0x0001aa0	# mode byte
./wbregs flashcfg 0x0001400	# empty byte, switching directions
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001400	# Read a byte of data
./wbregs flashcfg
./wbregs flashcfg 0x0001500	# Raise (deactivate) CS_n
./wbregs flashcfg 0x0000100	# Return to user mode

./wbregs 0x00800000
./wbregs 0x00800004
./wbregs 0x00800008
./wbregs 0x0080000c
./wbregs 0x00800010
./wbregs 0x00800014
./wbregs 0x00800018
./wbregs 0x0080001c
./wbregs 0x00800020
./wbregs 0x00800024
./wbregs 0x00800028
./wbregs 0x0080002c
