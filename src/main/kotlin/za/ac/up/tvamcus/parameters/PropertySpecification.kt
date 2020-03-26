package za.ac.up.tvamcus.parameters

/**
 * Information for evaluation of [timestepTemplate]
 *
 * @param type "liveness" or "reachability"
 * @param location progressLocationId if type is liveness, else errorLocationId
 * @param processList list of processes to be considered
 * @param operator (| or &) indicates if processList should be conjuncted or disjoined
 * @param fairnessON if TRUE then fairness should be checked
 */
data class PropertySpecification(
    val type: String,
    val location: Int,
    val processList: List<Int>,
    val operator: String,
    val fairnessON: Boolean = false,
    val doubleTest: Boolean = false
)
