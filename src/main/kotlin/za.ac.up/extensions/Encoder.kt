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

    data class ConjunctOver<T>(val conjunctOver: List<T>)

    data class DisjoinOver<T>(val disjoinOver: MutableList<T> = mutableListOf())

    /**
     * Information for evaluation of [encodedModelTemplate]
     *
     * @param type "liveness" or "reachability"
     * @param location progressLocationId if type is liveness, else errorLocationId
     * @param processList list of processes to be considered
     * @param operator (| or &) indicates if processList should be conjuncted or disjoined
     * @param fairnessON if TRUE then fairness should be checked
     */
    data class Test(val type: String, val location: Int, val processList: List<Int>, val operator: String, val fairnessON: Boolean = false)

    /**
     * An encoded transition as an encoded guard and a list of encoded assignments
     *
     * @param guard encoded guard
     * @param assignments list of encoded assignments
     */
    data class Transition(val guard: String, val assignments: ConjunctOver<String>)

    /**
     * Two nodes and the transition between them, all encoded
     *
     * @param parentProcess id of process to whom this belongs
     * @param oldLocation location from which transition originated, encoded
     * @param transition the transition between the nodes, encoded
     * @param newLocation location to which transition goes, encoded
     * @param idle list created when [idleAllExcept] has been called on all processes save the [parentProcess]
     */
    data class Link(
        val parentProcess: Int,
        val oldLocation: String,
        val transition: Transition,
        val newLocation: String,
        val idle: ConjunctOver<String>
    )

    /**
     * Encoded [model] using three valued abstraction
     *
     * Contains general timestamp indicators i and I (denoting i + 1) to be replaced upon formula creation with non-negative integers
     */
    private val encodedModelTemplate: DisjoinOver<Link> = DisjoinOver()

    private data class StepStat(
        val locationStatus: MutableList<String>,
        val predicateStatus: MutableList<String>,
        val fairnessStatus: MutableList<String>,
        val reRdStatus: Pair<String, String>
    )
    companion object {
        private val ff = FormulaFactory()
        private val p = PropositionalParser(ff)
        private val solver: MiniSat = MiniSat.glucose(ff)
    }
    init {
        encodeModel()
    }

    /**
     * Encodes location
     * by Definition 7
     *
     * @param pId ID of process the location belongs to
     * @param timestamp the timestamp location is encoded for, by default placeholder "i" is used
     * @return enc(loc_i)
     */
    private fun Int.encLocation(pId: Int, timestamp: String = "i"): String {
        val digit = digitRequired(model.processes[pId].numberOfLocations())
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

    /**
     * Encodes location as copy
     * by an extension of Definition 7
     *
     * @param pId ID of process the location belongs to
     * @param timestamp the timestamp location is encoded for (by default placeholder "i" is used)
     * @return enc(loc_i) copy
     */
    private fun Int.encLocationCopy(pId: Int, timestamp: String = "i"): String {
        val digit = digitRequired(model.processes[pId].numberOfLocations())
        var output = ""
        var binaryId = this.toBinaryString()
        while(binaryId.length < digit) {
            binaryId = "0$binaryId"
        }
        for((d, c) in binaryId.withIndex()) {
            val atomC = "n_${timestamp}_${pId}_${d}_c"
            output +=  if(c == '1') {
                "$atomC & "
            } else {
                "~$atomC & "
            }
        }
        return "(${output.dropLast(3)})"
    }

    /**
     * Creates the binary representation of an integer from a decimal input
     *
     * @return binary string of input integer
     */
    private fun Int.toBinaryString(): String {
        return if(this / 2 > 0) {
            "${(this / 2).toBinaryString()}${this % 2}"
        } else {
            "${this % 2}"
        }
    }

    /**
     * Encodes the setting true of the predicate it is called on
     * by Definition 8
     *
     * @param timestamp the timestamp predicate will become true on (by default placeholder "I" is used)
     * @return enc(p = true)
     */
    private fun String.encSetTrue(timestamp: String = "I"): String {
        return "(~${this}_${timestamp}_u & ${this}_${timestamp}_t)"
    }
    /**
     * Encodes a copy of the-setting-true-of the predicate it is called on
     * by Definition 8
     *
     * @param timestamp the timestamp predicate will become true on (by default placeholder "I" is used)
     * @return enc(p = true) copy
     */
    private fun String.encSetTrueCopy(timestamp: String = "I"): String {
        return "(~${this}_${timestamp}_u_c & ${this}_${timestamp}_t_c)"
    }

    /**
     * Encodes the setting-false-of the predicate it is called on
     * by Definition 8
     *
     * @param timestamp the timestamp predicate will become true on (by default placeholder "I" is used)
     * @return enc(p = false)
     */
    private fun String.encSetFalse(timestamp: String = "I"): String {
        return "(~${this}_${timestamp}_u & ~${this}_${timestamp}_t)"
    }
    /**
     * Encodes a copy of the setting-false-of the predicate it is called on
     * by Definition 8
     *
     * @param timestamp the timestamp predicate will become true on (by default placeholder "I" is used)
     * @return enc(p = false) copy
     */
    private fun String.encSetFalseCopy(timestamp: String = "I"): String {
        return "(~${this}_${timestamp}_u_c & ~${this}_${timestamp}_t_c)"
    }

    /**
     * Encodes the setting-unknown-of the predicate it is called on
     * by Definition 8
     * @param timestamp the timestamp predicate will become true on (by default placeholder "I" is used)
     * @return enc(p = unknown)
     */
    private fun String.encSetUnknown(timestamp: String = "I"): String {
        return "${this}_${timestamp}_u"
    }

    /**
     * Encodes the predicate (a string representation of an int) it is called on
     * by Definition 9
     *
     * @param timestamp the timestamp predicate is encoded for (by default placeholder "i" is used)
     * @return enc(p)
     */
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

    /**
     * Encodes the expression it is called on
     * by Definition 9
     *
     * @param timestamp the timestamp expression is encoded for (by default placeholder "i" is used)
     * @param negate if TRUE expression is negated before being encoded
     * @return enc(exp)
     */
    private fun String.encExp(timestamp: String = "i", negate: Boolean = false): String {
        var output = ""
        var predicate = ""
        var operator = ""
        var previousWasPredicate = false

        val expression = if(negate) {
            "(${p.parse(this).negate().nnf()})"
        } else {
            this
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

    /**
     * Encodes the guard it is called on
     * by Definition 9
     *
     * @return encoded guard
     */
    private fun String.encGuard(): String {
        return if (this.startsWith("choice(")) {
            val choices = this.drop(7).dropLast(1)
            encGuardChoice(
                choices.substringBefore(','),
                choices.substringAfter(',').dropWhile { it == ' ' }
            )
        } else {
            "(${p.parse(this).nnf()})".encExp()
        }
    }

    /**
     * Encodes a guard choice
     * by Definition 9
     *
     * @param left the left hand option of a guard choice
     * @param right the right hand option of a guard choice
     * @return encoded guard
     */
    private fun encGuardChoice(left: String, right: String): String {
        return if(left == "${'$'}true") {
            "${'$'}true"
        } else if(right == "${'$'}true") {
            "${'$'}false"
        } else if(left == "${'$'}false" && right == "${'$'}false") {
            "unknown"
        } else {
            "((${left.encExp()} | ${right.encExp(negate = true)}) & (${left.encExp()} | ${right.encExp()} | unknown))"
        }
    }

    /**
     * Sets node status for timestamp i equal to that of I for all processes save [activeProcess]
     * by Definition 10
     * note: timestamp i + 1 denoted as I
     *
     * @param activeProcess process to be excluded from idle
     * @return encoded idle processes for timestamp i to I
     */
    private fun idleAllExcept(activeProcess: Int): MutableList<String> {
        val conjunctOver = mutableListOf<String>()
        for((pId, p) in model.processes.withIndex()) {
            if(activeProcess != pId) {
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

    /**
     * Counts number of locations in process it is called on
     *
     * @return the number of locations (nodes) in target process
     */
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

    /**
     * Calculates the number of bits required to name a given amount of nodes using bits
     *
     * @param numLocations the number of locations that have to be named
     * @return the amount of bits required
     */
    private fun digitRequired(numLocations: Int): Int {
        return if (numLocations == 1) {
            1
        } else {
            ceil(log2(numLocations.toDouble())).toInt()
        }
    }

    /**
     * Encodes predicate assignment, based on choice([left], [right])
     * by Definition 10
     *
     * @param left left hand option
     * @param right right hand option
     * @param p the predicate to be assigned to TRUE, FALSE, or UNKNOWN
     */
    private fun encAssignmentChoice(left: String, right: String, p: String): String {
        return if (left == "${'$'}true" && left == "${'$'}false") {
            p.encSetTrue()
        } else if (left == "${'$'}false" && right == "${'$'}true") {
            p.encSetFalse()
        } else if (right == "${'$'}false" && left == "${'$'}false") {
            p.encSetUnknown()
        } else {
            "((${left.encExp()} & ${p.encSetTrue()}) | " +
            "(${right.encExp()} & ${p.encSetFalse()}) | " +
            "(${("($left | $right)").encExp(negate = true).replace("unknown", "${'$'}true")} & ${p.encSetUnknown()}))"
        }
    }

    /**
     * Encodes the predicate it is called on, based on [input]
     * by Definition 10
     *
     * If assignment is not a choice() turn it into one and call [encAssignmentChoice]
     *
     * @param input data on how to assign the predicate
     * @return encoded assignment
     */
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

    /**
     * Sets all predicates, save [toIgnore], equal to themselves for the next timestamp
     * by Definition 10
     *
     * @param toIgnore list of predicates that should have the ability to change
     * @return [ConjunctOver] of logical expressions of the form p_i <=> p_I
     */
    private fun keepPredicatesStable(toIgnore: MutableList<Int>): ConjunctOver<String> {
        val bigAnd = mutableListOf<String>()
        if(model.predicates.isEmpty()) {
            return ConjunctOver(bigAnd)
        }
        for(predicate in model.predicates) {
            val p = predicate.value.toString()
            if(!toIgnore.contains(predicate.value)) {
                bigAnd.add("(${p.encSetTrue("i")} <=> ${p.encSetTrue("I")}) & (${p.encSetUnknown("i")} <=> ${p.encSetUnknown("I")})")
            }
        }
        return ConjunctOver(bigAnd)
    }

    /**
     * Encodes the transition it is called on
     * by Definition 10
     *
     * @return encoded transition
     */
    private fun Parser.Transition.encTransition(): Transition {
        val butChange = mutableListOf<Int>()
        val conjunctOver = mutableListOf<String>()
        for(a in this.assignments) {
            butChange.add(a.predicate)
            conjunctOver.add("${a.predicate}".encAssignTo(a.RHS))
        }
        return Transition(guard = this.guard.encGuard(), assignments = keepPredicatesStable(butChange))
    }

    /**
     * Instantiates the [encodedModelTemplate] by encoding the entire [model]
     */
    private fun encodeModel() {
        for((pId, process) in model.processes.withIndex()) {
            for (t in process.transitions) {
                encodedModelTemplate.disjoinOver.add(
                    Link(
                        pId,
                        (t.source).encLocation(pId, "i"),
                        t.encTransition(),
                        (t.destination).encLocation(pId, "I"),
                        ConjunctOver(idleAllExcept(pId))
                    )
                )
            }


        }
        println("...modelEncoded")
    }

    //=====================================================================================================================
    //===================================================== Evaluator =====================================================
    //=====================================================================================================================
    /**
     * The tool used to evaluate [model] by using [encodedModelTemplate]
     *
     * @param test the properties of [model] to be tested on [encodedModelTemplate]
     */
    inner class Evaluator(private val test: Test) {

        private val predicates = mutableListOf<String>()
        init {
            if (test.type == "liveness") {
                derivePredicates()
            }
        }
        /**
         * Derives the full list of predicates that are in [encodedModelTemplate]
         * and adds them to [predicates] for future use
         */
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

        /**
         * Creates timestamp specific formula from [encodedModelTemplate]
         *
         * @param t timestamp to create formula for
         * @return the encoded [model] formula for timestamp [t]
         */
        private fun formulaForTimestamp(t: Int): Formula {
            val bigOr = mutableListOf<Formula>()
            for (link in encodedModelTemplate.disjoinOver) {
                bigOr.add(link toFormulaWithTimestamp t)
            }
            return ff.or(bigOr)
        }

        /*private fun Formula.modifiedWith(wString: String): Formula {
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
        }*/

        /**
         * Creates timestamp specific formula from [Transition] it is called on
         *
         * @param t timestamp to create formula for
         * @return the encoded [model] formula for timestamp [t]
         */
        private infix fun Transition.toFormulaWithTimestamp(t: Int): Formula {
            val assignmentsFormula = mutableListOf<Formula>()
            assignmentsFormula.add(
                p.parse(guard insertTimestamp t)
            )
            assignments.conjunctOver.forEach {
                assignmentsFormula.add(p.parse(it insertTimestamp t))
            }
            return ff.and(assignmentsFormula)
        }

        /**
         * Replaces i in the string it was called on with [t] and I with ([t] + 1)
         *
         * @param t timestamp to insert into string
         * @return string with [t] inserted where placeholders were
         */
        private infix fun String.insertTimestamp(t: Int): String {
            return this.replace("i", "$t").replace("I", "${t + 1}")
        }

        /**
         * Creates timestamp specific formula from the [Link] it is called on
         *
         * @param [t] timestamp to encode [Link] for
         * @return encoded formula of the [Link]
         */
        private infix fun Link.toFormulaWithTimestamp(t: Int): Formula {
            val idleFormula = mutableListOf<Formula>()
            idle.conjunctOver.forEach {
                idleFormula.add(p.parse(it insertTimestamp t))
            }
            return ff.and(
                p.parse(oldLocation insertTimestamp t),
                transition toFormulaWithTimestamp t,
                p.parse(newLocation insertTimestamp t),
                ff.and(idleFormula),
                if (test.type == "liveness") this.parentProcess.livenessEvaluationFormula(t) else null
            )
        }

        /**
         * by Definition?
         */
        private fun Int.livenessEvaluationFormula(t: Int): Formula {
            val bigAnd = mutableListOf<Formula>()
            encStateRecord().forEach {
                bigAnd.add(p.parse(it insertTimestamp t))
            }
            if (test.fairnessON) {
                bigAnd.add(p.parse("(fr_I_${this} <=> (re_i | rd_i))" insertTimestamp t))
                for(pId in model.processes.indices.filterNot{ it == this }) {
                    bigAnd.add(p.parse("(fr_${t + 1}_${pId} <=> fr_${t}_${pId})"))
                }
            }
            return ff.and(bigAnd)
        }

        /**
         * by Definition?
         */
        private fun encStateRecord(): List<String> {
            val bigAnd = mutableListOf<String>()
            bigAnd.add("(rd_I <=> (re_i | rd_i))")
            predicates.distinct().forEach {
                bigAnd.add(
                    "(${it.replace("i", "I")}_c <=> (((re_i & ~rd_i) => $it) & (~(re_i & ~rd_i) => ${it}_c)))"
                )
            }
            bigAnd.add("(lv_I <=> (lv_i | ((re_i | rd_i) & ${test.processList.encProgress()})))")
            return bigAnd
        }

        /**
         * helper function
         */
        private fun List<Int>.encProgress(): String {
            var progress = ""
            for (pId in this) {
                progress += test.location.encLocation(pId)
                progress += " ${test.operator} "
            }
            return progress.dropLast(3)
        }

        /**
         * by Definition 11/12?
         */
        private fun init(): Formula {
            val conjunctOver = mutableListOf<Formula>()
            for (pId in model.processes.indices) {
                conjunctOver.add(p.parse(0.encLocation(pId, timestamp = "0")))
                if (test.type == "liveness") {
                    conjunctOver.add(p.parse("~rd_0 & ~lv_0"))
                    conjunctOver.add(p.parse(0.encLocationCopy(pId, timestamp = "0")))
                    if(test.fairnessON) {
                        conjunctOver.add(p.parse("~fr_0_${pId}"))
                    }
                }
            }
            for (predicate in model.predicates) {
                val initAs: Boolean? = model.init[predicate.key]
                conjunctOver.add(
                    if (initAs != null && !initAs) {
                        p.parse(("${predicate.value}").encSetFalse(timestamp = "0"))
                    } else {
                        p.parse(("${predicate.value}").encSetTrue(timestamp = "0"))
                    }
                )
                if(test.type == "liveness") {
                    conjunctOver.add(
                        if (initAs != null && !initAs) {
                            p.parse(("${predicate.value}").encSetFalseCopy(timestamp = "0"))
                        } else {
                            p.parse(("${predicate.value}").encSetTrueCopy(timestamp = "0"))
                        }
                    )
                }
            }
            return ff.and(conjunctOver)
        }

        /**
         * Encodes location it is called on as the error location for timestamp [t]
         * by Definition 11/12?
         *
         * @param t timestamp for which location is deemed as the error location
         * @return formula of error location for timestamp [t]
         */
        private fun Int.errorLocation(t: Int = 10): Formula {
            val toJoin = mutableListOf<Formula>()
            for (pId in test.processList) {
                toJoin.add(p.parse(this.encLocation(pId, timestamp = t.toString())))
            }
            return if (test.operator == "|") ff.or(toJoin) else ff.and(toJoin)
        }

        /**
         * by Definition?
         */
        private fun livenessProperty(t: Int): Formula {
            val bigAnd = mutableListOf<Formula>()
            bigAnd.add(p.parse("rd_$t"))
            predicates.forEach { bigAnd.add(p.parse("(${it.insertTimestamp(t)} <=> ${it.insertTimestamp(t)}_c)")) }
            bigAnd.add(p.parse("~lv_$t"))
            if(test.fairnessON) {
                for(pId in model.processes.indices) {
                    bigAnd.add(p.parse("fr_${t}_$pId"))
                }
            }
            return ff.and(bigAnd)
        }

        private fun SortedSet<Literal>.reRdStatus(t: Int): Pair<String, String> {
            return Pair(
                if (this.contains(ff.literal("re_$t", true))) "re = true" else "re = false",
                if (this.contains(ff.literal("rd_$t", true))) "rd = true" else "rd = false"
            )
        }

        private fun SortedSet<Literal>.predicateStatus(t: Int): MutableList<String> {
            val predicateStatuses = mutableListOf<String>()
            for(p in model.predicates) {
                if(this.contains(ff.literal("${p.value}_${t}_u", true))) {
                    predicateStatuses.add("${p.key} = unknown")
                } else if (this.contains(ff.literal("${p.value}_${t}_t", true))) {
                    predicateStatuses.add("${p.key} = true")
                } else {
                    predicateStatuses.add("${p.key} = false")
                }
            }
            return predicateStatuses
        }

        private fun SortedSet<Literal>.fairnessStatus(t: Int): MutableList<String> {
            val fairnessVariableStatuses = mutableListOf<String>()
            for(pId in model.processes.indices) {
                if(this.contains(ff.literal("fr_${t}_${pId}", true))) {
                    fairnessVariableStatuses.add("P$pId = fair")
                } else {
                    fairnessVariableStatuses.add("P$pId = unfair")
                }
            }
            return fairnessVariableStatuses
        }

        private fun SortedSet<Literal>.locationStatus(t: Int): MutableList<String> {
            val processLocations = mutableListOf<String>()
            for ((pId, process) in model.processes.withIndex()) {
                var processLocation = ""
                for(d in 0 until digitRequired(process.numberOfLocations())) {
                    processLocation += if(this.contains(ff.literal("n_${t}_${pId}_${d}", false))) {
                        "0"
                    } else {
                        "1"
                    }
                }
                processLocations.add(processLocation)
            }
            return processLocations
        }

        private fun SortedSet<Literal>.pathInfo(bound: Int): MutableList<StepStat> {
            val steps = mutableListOf<StepStat>()
            for(k in 0 until bound + 1) {
                steps.add(
                    StepStat(
                        this.locationStatus(k),
                        this.predicateStatus(k),
                        this.fairnessStatus(k),
                        this.reRdStatus(k)
                    )
                )

            }
            return steps
        }

        private fun MutableList<StepStat>.print() {
            this.forEachIndexed { index, stepStat ->
                println("\n$index:")
                println(stepStat.locationStatus)
                println(stepStat.predicateStatus)
                println(stepStat.fairnessStatus)
                println(stepStat.reRdStatus)
            }
        }

        /*fun evaluate(bound: Int): Boolean {
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
        }*/

        /**
         *
         */
        fun evaluateNoOptimization(bound: Int) {
            val performanceLog = mutableListOf<Long>()
            val stepResults = mutableListOf<Tristate>()
            val startTime = System.nanoTime()
            var formula = init()
            for (t in 0 until bound + 1) {
                val property = if (test.type == "liveness") livenessProperty(t) else test.location.errorLocation(t)
                print(" k(a)=$t")
                val unitStartTimeA = System.nanoTime()
                solver.reset()
                solver.add(ff.and(formula, property, p.parse("unknown")))
                stepResults.add(solver.sat())
                performanceLog.add(System.nanoTime() - unitStartTimeA)
                printStepStat(performanceLog.last(), stepResults.last().toString())
                if (stepResults.last() == Tristate.TRUE) {
                    val pathInfo = solver.model().literals().pathInfo(t)
                    print(" k(b)=$t")
                    val unitStartTimeB = System.nanoTime()
                    solver.reset()
                    solver.add(ff.and(formula, property, p.parse("~unknown")))
                    stepResults.add(solver.sat())
                    performanceLog.add(System.nanoTime() - unitStartTimeB)
                    printStepStat(performanceLog.last(), stepResults.last().toString())
                    if (stepResults.last() == Tristate.TRUE) {
                        val time = System.nanoTime()
                        println("\nError Path")
                        solver.model().literals().pathInfo(t).print()
                        printSatisfiable(startT = startTime, endT = time, timestamp = t)
                        return
                    } else {
                        val time = System.nanoTime()
                        pathInfo.print()
                        printUnknown(startT = startTime, endT = time, timestamp = t)
                        return
                    }
                }
                formula = ff.and(formula, formulaForTimestamp(t))
            }
            printNoErrorFound(startTime, System.nanoTime(), bound)
        }
    }
}

