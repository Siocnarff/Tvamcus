package za.ac.up.extensions

import org.logicng.datastructures.Tristate
import org.logicng.formulas.Formula
import org.logicng.formulas.FormulaFactory
import org.logicng.formulas.Literal
import org.logicng.io.parsers.PropositionalParser
import org.logicng.solvers.MiniSat
import kotlin.math.ceil
import kotlin.math.log2


class Encoder (private val model: Parser.Model) {

    private val formulaTemplate: MutableList<Link> = mutableListOf()
    private var startTime: Long = 0

    private data class Link(
        val oldLocation: String,
        val transition: Transition,
        val newLocation: String,
        val idle: MutableList<String>
    )

    private data class Transition(val guard: String, val assignments: MutableList<String>)

    companion object {
        private val ff = FormulaFactory()
        private val p = PropositionalParser(ff)
        private val solver = MiniSat.glucose(ff)
    }

    init {
        startTime = System.nanoTime()
        encodeModel()
    }

    //by Definition 7
    private fun Int.encLocation(timestamp: String = "i", pId: Int, digit: Int): String {
        var output = ""
        var binaryId = this.toBinaryString()
        while(binaryId.length < digit) {
            binaryId = "0$binaryId"
        }
        for((d, c) in binaryId.withIndex()) {
            val atom = "n_${timestamp}_${pId}_${d}"
            output +=  if(c == '1') {
                "$atom & "
            } else {
                "~$atom & "
            }
        }
        return "(${output.dropLast(3)})"
    }

    private fun Int.encLocationForLit(timestamp: String = "i", pId: Int, digit: Int): MutableList<Literal> {
        val literals = mutableListOf<Literal>()
        var binaryId = this.toBinaryString()
        while(binaryId.length < digit) {
            binaryId = "0$binaryId"
        }
        for((d, c) in binaryId.withIndex()) {
            val atom = "n_${timestamp}_${pId}_${d}"
            if(c == '1') {
                literals.add(ff.literal(atom, true))
            } else {
                literals.add(ff.literal(atom, false))
            }
        }
        return literals
    }

    //by Definition 8
    private fun String.encSetTrue(timestamp: String = "I"): String {
        return "(~${this}_${timestamp}_u & ${this}_${timestamp}_t)"
    }

    //by Definition 8
    private fun String.encSetFalse(timestamp: String = "I"): String {
        return "(~${this}_${timestamp}_u & ~${this}_${timestamp}_t)"
    }

    //by Definition 8
    private fun String.encSetUnknown(timestamp: String = "I"): String {
        return "${this}_${timestamp}_u"
    }

    //by Definition 9
    private fun String.encPredicate(timestamp: String = "i"): String {
        if (this == "") {
            return ""
        }
        return if (this[0] == '~') {
            when (val p = this.substring(1)) {
                "${'$'}true" -> "${'$'}false"
                "${'$'}false" -> "${'$'}true"
                else -> "((${p}_${timestamp}_u & unknown) | (~${p}_${timestamp}_u & ~${p}_${timestamp}_t))"
            }
        } else {
            when (this) {
                "${'$'}true" -> "${'$'}true"
                "${'$'}false" -> "${'$'}false"
                else -> "((${this}_${timestamp}_u & unknown) | (~${this}_${timestamp}_u & ${this}_${timestamp}_t))"
            }
        }
    }

    //by Definition 9
    private fun encExp(input: String, timestamp: String = "i", negate: Boolean = false): String {
        var output = ""
        var predicate = ""
        var operator = ""
        var previousWasPredicate = false

        val expression = if(negate) {
            "(${p.parse(input).negate().nnf().toString()})"
        } else {
            input
        }

        for (c in expression) {
            if (c == ' ' || c == '&' || c == '|' || c == '(' || c == ')') {
                if (previousWasPredicate) {
                    if (predicate != "") {
                        output += predicate.encPredicate(timestamp)
                        predicate = ""
                    }
                    operator += c
                    previousWasPredicate = false
                } else {
                    operator += c
                }
            } else {
                if (!previousWasPredicate) {
                    if (operator != "") {
                        output += operator
                        operator = ""
                    }
                    predicate += c
                    previousWasPredicate = true
                } else {
                    predicate += c
                }
            }
        }
        return if (output == "") {
            predicate.encPredicate(timestamp)
        } else {
            output + operator
        }
    }

    //by Definition 9
    private fun encGuard(input: String): String {
        return if (input.startsWith("choice(")) {
            encGuardChoice(
                input.substring(7, input.indexOf(',')),
                input.dropLast(1).substring(input.indexOf(',') + 2)
            )
        } else {
            encExp("(${p.parse(input).nnf()})")
        }
    }

    //by Definition 9
    private fun encGuardChoice(left: String, right: String): String {
        return if(left == "${'$'}true") {
            "${'$'}true"
        } else if(right == "${'$'}true") {
            "${'$'}false"
        } else if(left == "${'$'}false" && right == "${'$'}false") {
            "unknown"
        } else {
            "((${encExp(left)} | ${encExp(right, negate = true)}) & (${encExp(left)} | ${encExp(right)} | unknown))"
        }
    }

    //by Definition 10
    private fun idleAllExcept(activeProcessId: Int): MutableList<String> {
        val conjunctOver = mutableListOf<String>()
        for((pId, p) in model.processes.withIndex()) {
            if(activeProcessId != pId) {
                val tally = numberOfLocations(p)
                for(locationId in 0..tally) {
                    for(d in 0..digitRequired(tally)) {
                        conjunctOver.add("(n_i_${pId}_${d} <=> n_I_${pId}_${d})")
                    }
                }
            }
        }
        return conjunctOver
    }

    //by Definition 10
    private fun encAssignmentChoice(left: String, right: String, p: String): String {
        return if (left == "${'$'}true" && left == "${'$'}false") {
            p.encSetTrue()
        } else if (left == "${'$'}false" && right == "${'$'}true") {
            p.encSetFalse()
        } else if (right == "${'$'}false" && left == "${'$'}false") {
            p.encSetUnknown()
        } else {
            "((${encExp(left)} & ${p.encSetTrue()}) | " +
            "(${encExp(right)} & ${p.encSetFalse()}) | " +
            "(${encExp("($left | $right)", negate = true).replace("unknown", "${'$'}true")} & ${p.encSetUnknown()}))"
        }
    }

    //by Definition 10
    private fun String.encAssignTo(input: String): String {
        return if (input.startsWith("choice(")) {
            encAssignmentChoice(
                input.substring(7, input.indexOf(',')),
                input.dropLast(1).substring(input.indexOf(',') + 2),
                this
            )
        } else {
            encAssignmentChoice(input, "~$input", this)
        }
    }

    //by Definition 10
    private fun keepPredicatesStable(toIgnore: MutableList<Int>): MutableList<String> {
        val conjunctOver = mutableListOf<String>()
        if(model.predicates.isEmpty()) {
            return conjunctOver
        }
        for(p in model.predicates) {
            if(!toIgnore.contains(p.value)) {
                conjunctOver.add(encAssignmentChoice("${p.value}", "~${p.value}", "${p.value}"))
            }
        }
        return conjunctOver
    }

    //by Definition 10
    private fun encTransition(t: Parser.Transition): Transition {
        val butChange = mutableListOf<Int>()
        val conjunctOver = mutableListOf<String>()
        for(a in t.assignments) {
            butChange.add(a.predicate)
            conjunctOver.add("${a.predicate}".encAssignTo(a.RHS))
        }
        conjunctOver.addAll(keepPredicatesStable(butChange))
        return Transition(guard = encGuard(t.guard), assignments = conjunctOver)
    }

    //by Definition 11/12?
    private fun init(): Formula {
        val conjunctOver = mutableListOf<Formula>()
        for((pId, process) in model.processes.withIndex()) {
            val digit = digitRequired(numberOfLocations(process))
            conjunctOver.add(p.parse(0.encLocation( "0", pId, digit)))
        }
        for(predicate in model.predicates) {
            conjunctOver.add(
                p.parse(("${predicate.value}").encSetTrue("0"))
            )
        }
        return ff.and(conjunctOver)
    }

    //by Definition 11/12?
    private fun errorLocation(e: Int, bound: Int = 10): Formula {
        val conjunctOver = mutableListOf<Formula>()
        for((pId, process) in model.processes.withIndex()) {
            val digit = digitRequired(numberOfLocations(process))
            conjunctOver.add(p.parse(e.encLocation(bound.toString(), pId, digit)))
        }
        return ff.and(conjunctOver)
    }

    private fun errorLocationForLit(e: Int, bound: Int = 10): MutableList<Literal> {
        val literals = mutableListOf<Literal>()
        for((pId, process) in model.processes.withIndex()) {
            val digit = digitRequired(numberOfLocations(process))
            literals += e.encLocationForLit(bound.toString(), pId, digit)
        }
        return literals
    }

    //this function creates our encoded formulaTemplate
    private fun encodeModel() {
        for((pId, process) in model.processes.withIndex()) {
            for (t in process.transitions) {
                val digit = digitRequired(numberOfLocations(process))
                formulaTemplate.add(
                        Link(
                            oldLocation = (t.source).encLocation("i", pId, digit),
                            transition = encTransition(t),
                            newLocation = (t.destination).encLocation("I", pId, digit),
                            idle = idleAllExcept(pId)
                        )
                )
            }
        }
        println("...modelEncoded")
    }

    fun evaluate(eLocation: Int, maxBound: Int): Boolean {
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
                //if(stepResults.last() == Tristate.TRUE) {
                if(true) {
                    printSatisfiable(startT = startTime, endT = System.nanoTime(), timestamp = t)
                    return true
                }
            }
            solver.add(ff.literal(w, true))
            formula = formulaForTimestamp(t)
        }
        printNoErrorFound(startTime, System.nanoTime(), maxBound)
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
                    printSatisfiable(startT = startTime, endT = System.nanoTime(), timestamp = t)
                    return true
                }
            }
            formula = formulaForTimestamp(t)
        }
        printNoErrorFound(startTime, System.nanoTime(), maxBound)
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
                    printSatisfiable(startT = startTime, endT = System.nanoTime(), timestamp = t)
                    println(stepResults)
                    return
                }
            }
            formula = ff.and(formula, formulaForTimestamp(t))
        }
        printNoErrorFound(startTime, System.nanoTime(), maxBound)
        println(stepResults)
    }

    private fun Formula.modifiedWith(wString: String): Formula {

        //now only works to modify locations of correctness
        val w = p.parse(wString)
        val disjointOver = mutableListOf(w)
        val conjunctOver = mutableListOf<Formula>()


        conjunctOver.add( ff.or(this, w.negate()))
        disjointOver.add( this.negate() )
        conjunctOver.add( ff.or(disjointOver) )

        return ff.and(conjunctOver)
    }

    //formula creation functions
    private fun formulaForTimestamp(t: Int): Formula {
        val bigOr = mutableListOf<Formula>()
        for(link in formulaTemplate) {
            bigOr.add(link toFormulaWithTimestamp t)
        }
        return ff.or(bigOr)
    }

    //modifies formula so as to be removable
    private infix fun Transition.toFormulaWithTimestamp(timestamp: Int): Formula {
        val assignmentsFormula = mutableListOf<Formula>()
        assignmentsFormula.add(
            p.parse(guard insertTimestamp timestamp)
        )
        assignments.forEach {
            assignmentsFormula.add(p.parse(it insertTimestamp timestamp))
        }
        return ff.and(assignmentsFormula)
    }

    //makes formula from formulaTemplate, using input timestamp as lower bound
    private infix fun Link.toFormulaWithTimestamp(t: Int): Formula {
        val idleFormula = mutableListOf<Formula>()
        idle.forEach{
            idleFormula.add(p.parse(it insertTimestamp t))
        }
        return ff.and(
            p.parse(oldLocation insertTimestamp t),
            transition toFormulaWithTimestamp  t,
            p.parse(newLocation insertTimestamp t),
            ff.and(idleFormula)
        )
    }

    //helper functions
    //========================================================
    private fun numberOfLocations(process: Parser.Process): Int {
        var tally = 0
        for (transition in process.transitions) {
            if (transition.source > tally) {
                tally = transition.source
            } else if (transition.destination > tally) {
                tally = transition.source
            }
        }
        return tally + 1
    }

    //returns the number of bits required to represent num locations using a binary string
    private fun digitRequired(numLocations: Int): Int {
        return if (numLocations == 1) {
            1
        } else {
            ceil(log2(numLocations.toDouble())).toInt()
        }
    }

    private infix fun String.insertTimestamp(t: Int): String {
        return this.replace("i", "$t").replace("I","${t + 1}")
    }

    private fun Int.toBinaryString(): String {
        return if(this / 2 > 0) {
            "${(this / 2).toBinaryString()}${this % 2}"
        } else {
            "${this % 2}"
        }
    }

    private fun printSatisfiable(startT: Long, endT: Long, timestamp: Int) {
        println()
        println("__________________________________________________________________________________________________")
        println()
        println()
        println("                               Satisfiable at timestamp: $timestamp")
        println("                               Time elapsed since start: ${(endT - startT)/1000000000}s")
        println()
        println("__________________________________________________________________________________________________")
    }

    private fun printStepStat(timeNs: Long) {
        println("....${timeNs/1000000}ms    ")
    }

    private fun printNoErrorFound(startT: Long, endT: Long, maxBound: Int) {
        println()
        println("No error found for bound of $maxBound")
        println("Total Time: ${(endT - startT)/1000000000}s")
    }
}

