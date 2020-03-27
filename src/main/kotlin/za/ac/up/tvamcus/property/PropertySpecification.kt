package za.ac.up.tvamcus.property

import za.ac.up.tvamcus.state.cfgs.CFGS

/**
 * Information for evaluation of [CFGS]
 *
 * @param type "liveness" or "reachability"
 * @param location progressLocationId if type is liveness, else errorLocationId
 * @param processList list of processes to be considered
 * @param operator (| or &) indicates if processList should be conjuncted or disjoined
 * @param fairnessOn if TRUE then fairness should be checked
 * @param multiModel if TRUE then MultiModel test approach should be used
 */
data class PropertySpecification(
    val type: String,
    val location: Int,
    val processList: List<Int>,
    val operator: Char,
    val fairnessOn: Boolean = false,
    val multiModel: Boolean = false,
    val cfgs: MutableList<CFGS> = mutableListOf()
)
