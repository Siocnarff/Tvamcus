package za.ac.up.extensions

fun printSatisfiable(startT: Long, endT: Long, timestamp: Int) {
    println()
    println("__________________________________________________________________________________________________")
    println()
    println()
    println("                               Satisfiable at timestamp: $timestamp")
    println("                               Time elapsed since start: ${(endT - startT)/1000000000}s  (${(endT - startT) / 1000000}ms)")
    println()
    println("__________________________________________________________________________________________________")
}

fun printStepStat(timeNs: Long, result: String) {
    println(" -> ${if (result == "TRUE") "T" else "F"}   ${timeNs/1000000}ms")
}

fun printNoErrorFound(startT: Long, endT: Long, maxBound: Int) {
    println()
    println("No error found for bound of $maxBound")
    println("Total Time: ${(endT - startT)/1000000000}s  (${(endT - startT)/10000000}ms)")
}