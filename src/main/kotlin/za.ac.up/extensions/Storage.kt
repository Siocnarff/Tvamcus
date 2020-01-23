package za.ac.up.extensions

/*private fun errorLocationForLit(e: Int, bound: Int = 10): MutableList<Literal> {
        val literals = mutableListOf<Literal>()
        for((pId, process) in model.processes.withIndex()) {
            val digit = digitRequired(numberOfLocations(process))
            literals += e.encLocationForLit(bound.toString(), pId, digit)
        }
        return literals
    }*/

/*fun evaluate(eLocation: Int, maxBound: Int): Boolean {
        val performanceLog = mutableListOf<Long>()
        val stepResults = mutableListOf<Tristate>()

        var formula = init()
        for(t in 0 until maxBound + 1) {
            val w = "w_${t}"
            val error = errorLocation(eLocation, t)
            val correct = error.negate().cnf()

            print("k(a)=$t")
            val unitStartTimeA = System.nanoTime()
            solver.add(formula)
            solver.add(correct.modifiedWith(w))
            stepResults.add(
                solver.sat(
                    mutableListOf(ff.literal("unknown", true), ff.literal(w, false))
                )
            )
            performanceLog.add(System.nanoTime() - unitStartTimeA)
            printStepStat(performanceLog.last())
            if(stepResults.last() == Tristate.TRUE) {
                print("k(b)=$t")
                val unitStartTimeB = System.nanoTime()
                stepResults.add(
                    solver.sat(
                        mutableListOf(ff.literal("unknown", false), ff.literal(w, false))
                    )
                )
                performanceLog.add(System.nanoTime() - unitStartTimeB)
                printStepStat(performanceLog.last())
                if(stepResults.last() == Tristate.TRUE) {
                    printSatisfiable(startT = startTime.last(), endT = System.nanoTime(), timestamp = t)
                    return true
                }
            }
            solver.add(ff.literal(w, true))
            formula = formulaForTimestamp(t)
        }
        printNoErrorFound(startTime.last(), System.nanoTime(), maxBound)
        return false
    }

    fun evaluateWithLiterals(eLocation: Int, maxBound: Int): Boolean {
        val performanceLog = mutableListOf<Long>()
        val stepResults = mutableListOf<Tristate>()


        var formula = init()
        for(t in 0 until maxBound + 1) {
            print("k(a)=$t")
            val unitStartTimeA = System.nanoTime()

            val errorA = errorLocationForLit(eLocation, t)
            errorA.add(ff.literal("unknown", true))

            solver.add(formula)
            stepResults.add(
                solver.sat(
                    errorA
                )
            )
            performanceLog.add(System.nanoTime() - unitStartTimeA)
            printStepStat(performanceLog.last())
            if(stepResults.last() == Tristate.TRUE) {
                print("k(b)=$t")
                val unitStartTimeB = System.nanoTime()
                val errorB = errorLocationForLit(eLocation, t)
                errorB.add(ff.literal("unknown", true))
                stepResults.add(
                    solver.sat(
                        errorB
                    )
                )
                performanceLog.add(System.nanoTime() - unitStartTimeB)
                printStepStat(performanceLog.last())
                if(stepResults.last() == Tristate.TRUE) {
                    printSatisfiable(startT = startTime.last(), endT = System.nanoTime(), timestamp = t)
                    return true
                }
            }
            formula = formulaForTimestamp(t)
        }
        printNoErrorFound(startTime.last(), System.nanoTime(), maxBound)
        return false
    }

    fun evaluateNoOptimization(eLocation: Int, maxBound: Int) {
        val performanceLog = mutableListOf<Long>()
        val stepResults = mutableListOf<Tristate>()

        var formula = init()
        for(t in 0 until maxBound) {
            val error = errorLocation(eLocation, t)

            println("k(a)=$t")
            val unitStartTimeA = System.nanoTime()
            solver.add(ff.and(formula, error, p.parse("unknown")))
            stepResults.add(solver.sat())
            solver.reset()
            performanceLog.add(System.nanoTime() - unitStartTimeA)
            printStepStat(performanceLog.last())
            if(stepResults.last() == Tristate.TRUE) {
                println("k(b)=$t")
                val unitStartTimeB = System.nanoTime()
                solver.add(ff.and(formula, error, p.parse("~unknown")))
                stepResults.add(solver.sat())
                solver.reset()
                performanceLog.add(System.nanoTime() - unitStartTimeB)
                printStepStat(performanceLog.last())
                if(stepResults.last() == Tristate.TRUE) {
                    printSatisfiable(startT = startTime.last(), endT = System.nanoTime(), timestamp = t)
                    println(stepResults)
                    return
                }
            }
            formula = ff.and(formula, formulaForTimestamp(t))
        }
        printNoErrorFound(startTime.last(), System.nanoTime(), maxBound)
        println(stepResults)
    }*/