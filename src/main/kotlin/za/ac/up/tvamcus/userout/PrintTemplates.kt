package za.ac.up.tvamcus.userout

fun printSatisfiable(time: Long, timestep: Int) {
    println()
    println("______________________________________________________________________")
    println()
    println()
    println("                 SATISFIABLE at timestep: $timestep")
    println("                 Time elapsed since start: ${time/1000000000}s  (${time/1000000}ms)")
    println()
    println("______________________________________________________________________")
}

fun printUnknown(time: Long, timestep: Int) {
    println()
    println("______________________________________________________________________")
    println()
    println()
    println("                UNKNOWN after timestep: $timestep")
    println("                Time elapsed since start: ${time/1000000000}s  (${time/1000000}ms)")
    println()
    println("_______________________________________________________________________")
}

fun printState(timeNs: Long, result: String) {
    println("${if (result == "TRUE") "True" else "False"}   ${timeNs/1000000}ms")
}

fun printNoErrorFound(time: Long, maxBound: Int) {
    println()
    println("No error found for bound of $maxBound")
    println("Total Time: ${time/1000000000}s  (${time/10000000}ms)")
}