package za.ac.up.tvamcus.userin

import org.apache.commons.cli.*
import za.ac.up.tvamcus.property.Config
import za.ac.up.tvamcus.parser.Parser
import za.ac.up.tvamcus.runner.Runner
import za.ac.up.tvamcus.state.cfgs.CFGS


object ArgCatcher {
    @JvmStatic
    fun main(args: Array<String>) {
        val cfgsParser = Parser()
        val clParser = DefaultParser()
        val options = setArgOptions()
        val cmd= clParser.parse(options, args)
        if(soundCommand(cmd)) {
            val option = if(cmd.hasOption("er")) "er" else "el"
            val eOptions = cmd.getOptionValues(option)
            val processes = if(cmd.hasOption("p")) cmd.getOptionValue("p") else "all"
            val models = mutableListOf<CFGS>(cfgsParser.parseFile("files/${eOptions[0]}.json"))
            if(cmd.hasOption("mm")) {
                models.add(cfgsParser.parseFile("files/${eOptions[0]}_0p.json"))
            }
            val conf = Config(
                LOCATION = eOptions[1].toInt(),
                BOUND = eOptions[2].toInt(),
                PROCESSES = processes.extractCSList(models.first()),
                DISJUNCT = cmd.hasOption("d"),
                LIVENESS = cmd.hasOption("el"),
                FAIRNESS = cmd.hasOption("f"),
                MULTI_MODEL = cmd.hasOption("f")
            )
            val runner = Runner(cfgs = models, config = conf)
            runner.evaluate()
        } else {
            printMalformedCommand(options)
        }
    }

    private fun printMalformedCommand(options: Options) {
        println("==========================")
        println("Your command was malformed")
        println("==========================")
        val formatter = HelpFormatter()
        formatter.printHelp("Tvamcus", options)
    }

    private fun setArgOptions(): Options {
        val options = Options()
        val efr = Option(
            "er",
            "evaluateReachability",
            true,
            "Evaluate reachability by any process in CFG model - args are JSON filename, error location and upper bound."
        )
        efr.args = 3
        options.addOption(efr)
        val efl = Option(
            "el",
            "evaluateLiveness",
            true,
            "Evaluate liveness of all processes in CFG model - args are JSON filename, error location and upper bound."
        )
        efl.args = 3
        options.addOption(efl)
        options.addOption(
            "f",
            "fair",
            false,
            "Enforce fairness."
        )
        options.addOption(
            "h",
            "help",
            false,
            "Print this help message."
        )
        options.addOption(
            "led",
            "locationEncodingDisjunct",
            false,
            "Use disjunction in error location encoding, if flag not specified error location encoding uses conjunction."
        )
        options.addOption(
            "mm",
            "multiModel",
            false,
            "Set evaluation to use the multi-model approach. NoP file must have same name as AllP file, only with _0P appended.")
        options.addOption(
            "p",
            "processes",
            true,
            "Accepts a comma-separated list of processes (by id) that should take part in evaluation, if not specified all processes take part."
        )
        return options
    }

    private fun soundCommand(cmd: CommandLine): Boolean {
        val userArgs = when {
            cmd.hasOption("er") -> {
                cmd.getOptionValues("er")
            }
            cmd.hasOption("el") -> {
                cmd.getOptionValues("el")
            }
            else -> {
                return false
            }
        }
        if(userArgs[1].toIntOrNull() == null || userArgs[2].toIntOrNull() == null) {
            return false
        }
        if(cmd.hasOption("p")) {
            val processes = cmd.getOptionValue("p").split(",")
            for (process in processes) {
                if(process.toIntOrNull() == null) { return false }
            }
        }
        return true
    }

    private fun String.extractCSList(model: CFGS): MutableList<Int> {
        val list = mutableListOf<Int>()
        if (this == "all") {
            model.processes.mapTo(list) { it.id }
        } else {
           this.split(",").mapTo(list) { it.toInt() }
        }
        return list
    }
}