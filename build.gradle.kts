plugins {
    kotlin("jvm") version "1.3.61"
}

group = "za.ac.up"
version = "1.0"

repositories {
    mavenCentral()
}

dependencies {
    implementation(kotlin("stdlib-jdk8"))
    implementation("com.google.code.gson:gson:2.8.5")
    implementation("org.logicng:logicng:1.6.1")
}

tasks {
    compileKotlin {
        kotlinOptions.jvmTarget = "1.8"
    }
    //compileTestKotlin {
    //    kotlinOptions.jvmTarget = "1.8"
    //}
    jar {
        manifest {
            attributes["Main-Class"] = "za.ac.up.CLI"
        }
        from(
            configurations.compileClasspath.get().map {
                if(it.isDirectory) it else zipTree(it)
            }
        )
    }
}