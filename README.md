                      Artifact for the manuscript: 
      Checking Robustness Between Weak Transactional Consistency Models


# Artifact description 

The directory ```boogie``` contains the source files of the Boogie program verifier version 2.4.1.10503
that we used in our development. The latest version of Boogie can be found here: https://github.com/boogie-org/boogie.

Each sub-directory ```Y``` of the ```examples``` directory contains the formalization for the application ```Y``` in the Boogie programming language.

For each application, the Boogie encoding of the original application is given in the file which ends with the word ```Original```.

For each application, a file which contains the word ```Instrumented``` is for a client program of the application that is a witness of a robustness violation.

For each application, a file which ends with the word ```Cmover``` contains the movers checking necessary for construction of the commutativity dependency graph. In the current version of the artifact, the graph is manually constructed based on the automated check of movers.

# How to test the artifact
 
NOTE:  Tested with Boogie program verifier version 2.4.1.10503.

## Steps

  0. Install ```boogie``` 
  1. Go to the ```examples``` directory
  2. RUN: /usr/bin/time -v --format="%e" %boogie -noinfer -typeEncoding:m -tracePOs -traceTimes  -trace  -useArrayTheory "%s" > "%t"
  3. RUN: %diff "%s.expect" "%t"
