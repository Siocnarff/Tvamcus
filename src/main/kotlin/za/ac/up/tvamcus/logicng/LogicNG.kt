package za.ac.up.tvamcus.logicng

import org.logicng.formulas.Formula
import org.logicng.formulas.FormulaFactory
import org.logicng.io.parsers.PropositionalParser
import org.logicng.solvers.MiniSat
import org.logicng.solvers.sat.GlucoseConfig
import org.logicng.solvers.sat.MiniSatConfig

object LogicNG {
    val ff = FormulaFactory()
    val p = PropositionalParser(ff)
    val solver: MiniSat = MiniSat.glucose(
        ff,
        MiniSatConfig.Builder().proofGeneration(true).incremental(false).build(),
        GlucoseConfig.Builder().build()
    )
}

fun parse(f: String): Formula {
    return LogicNG.p.parse(f)
}

fun conjunct(formulas: MutableCollection<Formula>): Formula {
    return LogicNG.ff.and(formulas)
}

fun conjunct(vararg v: Formula): Formula {
    val formulas = mutableListOf<Formula>()
    formulas.addAll(v)
    return LogicNG.ff.and(formulas)
}

fun disjoin(formulas: MutableCollection<Formula>): Formula {
    return LogicNG.ff.or(formulas)
}

fun disjoin(vararg v: Formula): Formula {
    val formulas = mutableListOf<Formula>()
    formulas.addAll(v)
    return LogicNG.ff.or(formulas)
}