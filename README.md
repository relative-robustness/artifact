                      Artifact for the manuscript: 
      Checking Robustness Between Weak Transactional Consistency Models


# DESCRIPTION of FILES

Each a sub-directory ```Y``` of the ```artifact``` directory contains 
the formalization for the application ```Y``` in the Boogie programming language. 
The full formalization of the application is given the file which its name 
ends with the word ```Original```.
A file which its name contains the word ```Instrumented``` contains 
a client program of the corresponding application that is a witness 
to a robustness violation. 
A file which its names ends with the word ```Cmover``` contains 
the movers checking necessary for building the commutativity 
dependency graph.
  


# How to Load Examples
 
NOTE:  Tested with Boogie program verifier version 2.4.1.10503.


## Steps

  0. Install ```boogie``` 
  1. Go to the ```artifact``` directory
  2. RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
  3. RUN: %diff "%s.expect" "%t"
