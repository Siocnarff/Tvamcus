2020/05/13

usage: Tvamcus
 -el,--evaluateLiveness <arg>       Evaluate liveness of all processes in
                                    CFG model - args are JSON filename,
                                    error location and upper bound.
 -er,--evaluateReachability <arg>   Evaluate reachability by any process
                                    in CFG model - args are JSON filename,
                                    error location and upper bound.
 -f,--fair                          Enforce fairness.
 -h,--help                          Print this help message.
 -led,--locationEncodingDisjunct    Use disjunction in error location
                                    encoding, if flag not specified error
                                    location encoding uses conjunction.
 -mm,--multiModel                   Set evaluation to use the multi-model
                                    approach. NoP file must have same name
                                    as AllP file, only with _0P appended.
 -p,--processes <arg>               Accepts a comma-separated list of
                                    processes (by id) that should take
                                    part in evaluation, if not specified
                                    all processes take part.


Notice that the following command will work

Find the jarfile already built in Tvamcus → build → libs

java -jar Tvamcus-1.0.jar -er 4philosophers 3 20 -p 0,1,2,3 -mm


To test any other files, place them in the same directory as the Tvamcus-1.0.jar file before running your command