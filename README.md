                      Artifact for the manuscript: 
      Checking Robustness Between Weak Transactional Consistency Models


# Artifact description 

The directory ```boogie``` contains the source files of the Boogie program verifier version 2.4.1.10503
that we used in our development. The latest version of Boogie can be found here: https://github.com/boogie-org/boogie.

Each a sub-directory ```Y``` of the ```examples``` directory contains  the formalization for the application ```Y``` in the Boogie programming language. 

The full formalization of the application is given the file which its name  ends with the word ```Original```.

A file which its name contains the word ```Instrumented``` contains  a client program of the corresponding application that is a witness  to a robustness violation. 

A file which its names ends with the word ```Cmover``` contains the movers checking necessary for building the commutativity dependency graph.

# How to test the artifact
 
NOTE:  Tested with Boogie program verifier version 2.4.1.10503.

## Steps

  0. Install ```boogie``` 
  1. Go to the ```examples``` directory
  2. RUN: /usr/bin/time -v --format="%e" %boogie -noinfer -typeEncoding:m -tracePOs -traceTimes  -trace  -useArrayTheory "%s" > "%t"
  3. RUN: %diff "%s.expect" "%t"
