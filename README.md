# CSE361S Malloc Lab TA Solution Guide

### Author: Nick Cochran
### Email: nickcochran02@gmail.com | c.nick@wustl.edu

## Note to Future TAs and Head TAs

Feel free to use this repo to help you in any way you see fit.

If you use this repo to create a new, better one (as I know I am not perfect),
    please still give me credit for the original work.

If you ever would like something added/modified, let me know and I will do my best to make that happen.

## Description

This repository serves as an easy way for TAs to reference code for each of the malloc lab implementations, 
especially because I intentionally made it so all changes for an implementation could be seen at the same time.

- Every commit is a new implementation for the malloc lab.
  - When it comes to later implementations, these are separate branches that are merged into main
        to make a clean commit history for each implementation that can be viewed in a single "commit".
  - **For these implementations click on "Merge pull request" in the commit history for the respective
    	implementation detailed later in the message to see the changes for the full commit history in that branch.**
- The commit message details which implementation the commit is for.
- Each function also has a changelog section detailing when changes have been made to that function.
    - This is meant to help identify which functions need to be changed for each implementation.
    - I did not flawlessly update the changelog for every change, but I did my best to keep it up to date.
- Ideally, if you would like,
    you can copy any of these functions to test with student code if further debugging is required.

#### Below is the original README for the Malloc Lab.

---



#############################
# CS:APP Malloc Lab
# Handout files for students
#############################

***********
Main Files:
***********

mm.{c,h}
        Your solution malloc package. mm.c is the file that you
        will be handing in, and is the only file you should modify.

Makefile
        Builds the driver 

mdriver.c
        The malloc driver that tests your mm.c file
        Once you've run make, run ./mdriver to test
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
