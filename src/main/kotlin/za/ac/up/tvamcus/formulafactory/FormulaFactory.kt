package za.ac.up.tvamcus.formulafactory

import org.logicng.formulas.Formula
import org.logicng.formulas.FormulaFactory
import org.logicng.io.parsers.PropositionalParser
import org.logicng.solvers.MiniSat

object Ff {
    val ff = FormulaFactory()
    val p = PropositionalParser(ff)
    val solver: MiniSat = MiniSat.glucose(ff)
}

fun parse(f: String): Formula {
    return Ff.p.parse(f)
}

fun conjunct(formulas: MutableCollection<Formula>): Formula {
    return Ff.ff.and(formulas)
}

fun conjunct(vararg v: Formula): Formula {
    val formulas = mutableListOf<Formula>()
    formulas.addAll(v)
    return Ff.ff.and(formulas)
}

fun disjoin(formulas: MutableCollection<Formula>): Formula {
    return Ff.ff.or(formulas)
}

fun disjoin(vararg v: Formula): Formula {
    val formulas = mutableListOf<Formula>()
    formulas.addAll(v)
    return Ff.ff.or(formulas)
}