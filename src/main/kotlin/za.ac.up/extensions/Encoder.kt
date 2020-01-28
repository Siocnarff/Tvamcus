package za.ac.up.extensions

import org.logicng.datastructures.Tristate
import org.logicng.formulas.Formula
import org.logicng.formulas.FormulaFactory
import org.logicng.formulas.Literal
import org.logicng.io.parsers.PropositionalParser
import org.logicng.solvers.MiniSat
import java.util.*
import kotlin.math.ceil
import kotlin.math.log2

class Encoder(private val model: Parser.Model) {

    data class Test(val type: String, val location: Int, val processList: String, val operator: String)
    data class Transition(val guard: String, val assignments: List<String>)
    data class Link(
        val oldLocation: String,
        val transition: Transition,
        val newLocation: String,
        val idle: List<String>
    )
    private val formulaTemplate: MutableList<Link> = mutableListOf()
    companion object {
        private val ff = FormulaFactory()
        private val p = PropositionalParser(ff)
        private val solver: MiniSat = MiniSat.glucose(ff)
    }
    init {
        encodeModel()
    }

    //=================================================================================================================
    //====== Encoding functions based on TVAMCUS paper are referred to by their definition numbers in said paper ======
    //=================================================================================================================

    //by Definition 7
    private fun Int.encLocation(timestamp: String = "i", pId: Int, digit: Int, copy: Boolean = false): String {
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
            if (copy) {
                val atomC = "n_${timestamp}_${pId}_${d}_c"
                output +=  if(c == '1') {
                    "$atomC & "
                } else {
                    "~$atomC & "
                }
            }
        }
        return "(${output.dropLast(3)})"
    }
    //helper function
    private fun Int.toBinaryString(): String {
        return if(this / 2 > 0) {
            "${(this / 2).toBinaryString()}${this % 2}"
        } else {
            "${this % 2}"
        }
    }

    //by Definition 8
    private fun String.encSetTrue(timestamp: String = "I", copy: Boolean = false): String {
        return "(~${this}_${timestamp}_u & ${this}_${timestamp}_t)${if (copy) {" & (~${this}_${timestamp}_u_c & ${this}_${timestamp}_t_c)"} else ""}"
    }

    //by Definition 8
    private fun String.encSetFalse(timestamp: String = "I", copy: Boolean = false): String {
        return "(~${this}_${timestamp}_u & ~${this}_${timestamp}_t)${if (copy) {" & (~${this}_${timestamp}_u_c & ~${this}_${timestamp}_t_c)"} else ""}"
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
            "(${p.parse(input).negate().nnf()})"
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
            val choices = input.drop(7).dropLast(1)
            encGuardChoice(
                choices.substringBefore(','),
                choices.substringAfter(',').dropWhile { it == ' ' }
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
                val tally = p.numberOfLocations()
                for(locationId in 0..tally) {
                    for(d in 0..digitRequired(tally)) {
                        conjunctOver.add("(n_i_${pId}_${d} <=> n_I_${pId}_${d})")
                    }
                }
            }
        }
        return conjunctOver
    }
    //helper function
    //counts locations in json model
    private fun Parser.Process.numberOfLocations(): Int {
        var tally = 0
        for (transition in this.transitions) {
            if (transition.source > tally) {
                tally = transition.source
            } else if (transition.destination > tally) {
                tally = transition.source
            }
        }
        return tally + 1
    }
    //helper function
    //returns number of bits required to represent num locations using a binary string
    private fun digitRequired(numLocations: Int): Int {
        return if (numLocations == 1) {
            1
        } else {
            ceil(log2(numLocations.toDouble())).toInt()
        }
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

    //this function creates our encoded formulaTemplate
    private fun encodeModel() {
        for((pId, process) in model.processes.withIndex()) {
            for (t in process.transitions) {
                val digit = digitRequired(process.numberOfLocations())
                formulaTemplate.add(
                    Link(
                        (t.source).encLocation("i", pId, digit),
                        encTransition(t),
                        (t.destination).encLocation("I", pId, digit),
                        idleAllExcept(pId)
                    )
                )
            }
        }
        println("...modelEncoded")
    }

    //=================================================================================================================
    //=================================================== Evaluator ===================================================
    //=================================================================================================================

    inner class Evaluator(private val test: Test) {

        private val predicates = mutableListOf<String>()
        private val processesToCheck = mutableListOf<Int>()

        init {
            processesToCheck += (test.processList).extractCSList()
            if (test.type == "liveness") {
                derivePredicates()
            }
        }

        //helper function
        private fun derivePredicates() {
            for (p in model.predicates) {
                predicates.add("${p.value}_i_u")
                predicates.add("${p.value}_i_t")
            }
            for ((pId, process) in model.processes.withIndex()) {
                for (d in 0 until digitRequired(process.numberOfLocations())) {
                    predicates.add("n_i_${pId}_${d}")
                }
            }
        }

        //helper function
        private fun String.extractCSList(): MutableList<Int> {
            var listTrimmed = this.dropLastWhile { it == ')' }.dropWhile { it == '(' }
            val list = mutableListOf<Int>()
            if (listTrimmed.decapitalize() == "all" || listTrimmed.decapitalize() == "a") {
                for (pId in model.processes.indices) {
                    list.add(pId)
                }
            } else {
                while (listTrimmed.contains(',')) {
                    list.add(listTrimmed.substringBefore(',').trim().toInt())
                    listTrimmed = listTrimmed.substringAfter(',').trim()
                }
                list.add(listTrimmed.toInt())
            }
            return list
        }

        //formula creation function
        private fun formulaForTimestamp(t: Int): Formula {
            val bigOr = mutableListOf<Formula>()
            for (link in formulaTemplate) {
                bigOr.add(link toFormulaWithTimestamp t)
            }
            return ff.or(bigOr)
        }

        private fun Formula.modifiedWith(wString: String): Formula {
            //now only works to modify locations of correctness
            println()
            println(this)
            println()
            val w = p.parse(wString)
            val disjointOver = mutableListOf(w)
            val conjunctOver = mutableListOf<Formula>()
            conjunctOver.add(ff.or(this, w.negate()))
            disjointOver.add(this.negate())
            conjunctOver.add(ff.or(disjointOver))
            return ff.and(conjunctOver)
        }

        //modifies formula so as to be removable from SAT memory by adding a "removal formula"
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

        //helper function
        private infix fun String.insertTimestamp(t: Int): String {
            return this.replace("i", "$t").replace("I", "${t + 1}")
        }

        //makes formula from formulaTemplate, using input timestamp as lower bound
        private infix fun Link.toFormulaWithTimestamp(t: Int): Formula {
            val idleFormula = mutableListOf<Formula>()
            val stateRecord = mutableListOf<Formula>()
            idle.forEach {
                idleFormula.add(p.parse(it insertTimestamp t))
            }
            if (test.type == "liveness") {
                encStateRecord().forEach {
                    stateRecord.add(p.parse(it insertTimestamp t))
                }
            }
            return ff.and(
                p.parse(oldLocation insertTimestamp t),
                transition toFormulaWithTimestamp t,
                p.parse(newLocation insertTimestamp t),
                ff.and(idleFormula),
                ff.and(stateRecord)
            )
        }

        //helper functions
        //by definition ?
        private fun encStateRecord(): List<String> {
            val bigAnd = mutableListOf<String>()
            bigAnd.add("(rd_I <=> (re_i | rd_i))")
            predicates.distinct().forEach {
                bigAnd.add(
                    "(${it.replace("i", "I")}_c <=> (((re_i & ~rd_i) => $it) & (~(re_i & ~rd_i) => ${it}_c)))"
                )
            }
            bigAnd.add("(lv_I <=> (lv_i | ((re_i | rd_i) & ${encProgress(processesToCheck)})))")
            return bigAnd
        }

        //helper function
        private fun encProgress(toCheck: MutableList<Int>): String {
            var progress = ""
            for (pId in toCheck) {
                val process = model.processes[pId]
                progress += test.location.encLocation(pId = pId, digit = digitRequired(process.numberOfLocations()))
                progress += " ${test.operator} "
            }
            return progress.dropLast(3)
        }

        //by Definition 11/12?
        private fun init(): Formula {
            val conjunctOver = mutableListOf<Formula>()
            for ((pId, process) in model.processes.withIndex()) {
                val digit = digitRequired(process.numberOfLocations())
                conjunctOver.add(p.parse(0.encLocation("0", pId, digit, copy = (test.type == "liveness"))))
            }
            for (predicate in model.predicates) {
                val initAs: Boolean? = model.init[predicate.key]
                conjunctOver.add(
                    if (initAs != null && !initAs) {
                        p.parse(("${predicate.value}").encSetFalse("0", copy = (test.type == "liveness")))
                    } else {
                        p.parse(("${predicate.value}").encSetTrue("0", copy = (test.type == "liveness")))
                    }
                )
            }
            if (test.type == "liveness") {
                conjunctOver.add(p.parse("~rd_0 & ~lv_0"))
            }
            return ff.and(conjunctOver)
        }

        //by Definition 11/12?
        private fun errorLocation(e: Int, bound: Int = 10): Formula {
            val toJoin = mutableListOf<Formula>()
            for (pId in processesToCheck) {
                val process = model.processes[pId]
                val digit = digitRequired(process.numberOfLocations())
                toJoin.add(p.parse(e.encLocation(bound.toString(), pId, digit)))
            }
            return if (test.operator == "|") ff.or(toJoin) else ff.and(toJoin)
        }

        private fun livenessProperty(t: Int): Formula {
            val bigAnd = mutableListOf<Formula>()
            bigAnd.add(p.parse("rd_$t"))
            predicates.forEach { bigAnd.add(p.parse("(${it.insertTimestamp(t)} <=> ${it.insertTimestamp(t)}_c)")) }
            bigAnd.add(p.parse("~lv_$t"))
            return ff.and(bigAnd)
        }

        private fun SortedSet<Literal>.predicateStatus(timestamp: Int): MutableList<String> {
            val predicateStatuses = mutableListOf<String>()
            for(p in model.predicates) {
                if(this.contains(ff.literal("${p.value}_${timestamp}_u", true))) {
                    predicateStatuses.add("${p.key} = unknown")
                } else if (this.contains(ff.literal("${p.value}_${timestamp}_t", true))) {
                    predicateStatuses.add("${p.key} = true")
                } else {
                    predicateStatuses.add("${p.key} = false")
                }
            }
            return predicateStatuses
        }

        private fun SortedSet<Literal>.locationStatus(timestamp: Int): MutableList<String> {
            val processLocations = mutableListOf<String>()
            for ((pId, process) in model.processes.withIndex()) {
                var processLocation = ""
                for(d in 0 until digitRequired(process.numberOfLocations())) {
                    processLocation += if(this.contains(ff.literal("n_${timestamp}_${pId}_${d}", false))) {
                        "0"
                    } else {
                        "1"
                    }
                }
                processLocations.add(processLocation)
            }
            return processLocations
        }

        private fun SortedSet<Literal>.printSolutionPath(bound: Int) {
            for(k in 0 until bound + 1) {
                println("\n$k:")
                println(this.locationStatus(k))
                println(this.predicateStatus(k))
            }
        }

        fun evaluate(bound: Int): Boolean {
            val performanceLog = mutableListOf<Long>()
            val stepResults = mutableListOf<Tristate>()
            val startTime = System.nanoTime()

            var formula = init()
            for (t in 0 until bound + 1) {
                val w = "w_${t}"
                val property = if (test.type == "liveness") livenessProperty(t) else errorLocation(test.location, t)
                val correct = property.negate().cnf()

                print(" k(a)=$t")
                val unitStartTimeA = System.nanoTime()
                println(property)
                solver.add(formula)
                solver.add(correct.modifiedWith(w))
                stepResults.add(
                    solver.sat(
                        mutableListOf(ff.literal("unknown", true), ff.literal(w, false))
                    )
                )
                performanceLog.add(System.nanoTime() - unitStartTimeA)
                printStepStat(performanceLog.last(), stepResults.last().toString())
                if (stepResults.last() == Tristate.TRUE) {
                    print(" k(b)=$t")
                    val unitStartTimeB = System.nanoTime()
                    stepResults.add(
                        solver.sat(
                            mutableListOf(ff.literal("unknown", false), ff.literal(w, false))
                        )
                    )
                    performanceLog.add(System.nanoTime() - unitStartTimeB)
                    printStepStat(performanceLog.last(), stepResults.last().toString())
                    if (stepResults.last() == Tristate.TRUE) {
                        printSatisfiable(startT = startTime, endT = System.nanoTime(), timestamp = t)
                        return true
                    }
                }
                solver.add(ff.literal(w, true))
                formula = formulaForTimestamp(t)
            }
            printNoErrorFound(startTime, System.nanoTime(), bound)
            return false
        }

        fun evaluateNoOptimization(bound: Int) {
            val performanceLog = mutableListOf<Long>()
            val stepResults = mutableListOf<Tristate>()
            val startTime = System.nanoTime()
            var formula = init()
            for (t in 0 until bound + 1) {
                val property = if (test.type == "liveness") livenessProperty(t) else errorLocation(test.location, t)
                print(" k(a)=$t")
                val unitStartTimeA = System.nanoTime()
                solver.reset()
                solver.add(ff.and(formula, property, p.parse("unknown")))
                stepResults.add(solver.sat())
                performanceLog.add(System.nanoTime() - unitStartTimeA)
                printStepStat(performanceLog.last(), stepResults.last().toString())
                if (stepResults.last() == Tristate.TRUE) {
                    print(" k(b)=$t")
                    val unitStartTimeB = System.nanoTime()
                    solver.reset()
                    solver.add(ff.and(formula, property, p.parse("~unknown")))
                    stepResults.add(solver.sat())
                    performanceLog.add(System.nanoTime() - unitStartTimeB)
                    printStepStat(performanceLog.last(), stepResults.last().toString())
                    if (stepResults.last() == Tristate.TRUE) {
                        printSatisfiable(startT = startTime, endT = System.nanoTime(), timestamp = t)
                        println("\nSolution Path")
                        solver.model().literals().printSolutionPath(t)
                        return
                    }
                }
                formula = ff.and(formula, formulaForTimestamp(t))
            }
            printNoErrorFound(startTime, System.nanoTime(), bound)
        }
    }
}

