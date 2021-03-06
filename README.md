# Memory Allocator

Built using segregated lists. 

Uses the best-fit policy, and a first-in, last-out policy.

***********
Main Files:
***********

mm.{c,h}
        Your solution malloc package. mm.c is the file that you
        will be handing in, and is the only file you should modify.

Makefile
        Builds the driver 

mdriver.c
        The malloc driver that tests the mm.c file
        After running make, run ./mdriver to test
        your solution. 

traces/
	Directory that contains the trace files that the driver uses
	to test your solution. Files with names of the form XXX-short.rep
	contain very short traces that you can use for debugging.

**********************************
Other support files for the driver
**********************************
config.h	Configures the malloc lab driver
clock.{c,h}	Low-level timing functions
fcyc.{c,h}	Function-level timing functions
memlib.{c,h}	Models the heap and sbrk function
stree.{c,h}     Data structure used by the driver to check for
		overlapping allocations

*******************************
Building and running the driver
*******************************
To build the driver, type "make" to the shell.

To run the driver on a tiny test trace:

	unix> ./mdriver -V -f traces/syn-array-short.rep

To get a list of the driver flags:

	unix> ./mdriver -h

The -V option prints out helpful tracing information
