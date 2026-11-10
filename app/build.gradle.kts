plugins {
    id("com.android.application")
    id("org.jetbrains.kotlin.android")
}
android {
    namespace = "com.concertcam"
    compileSdk = 34
    defaultConfig {
        applicationId = "com.concertcam"
        minSdk = 30
        targetSdk = 34
        versionCode = (project.findProperty("vc") as String?)?.toInt() ?: 1
        versionName = "1.0"
    }
    signingConfigs {
        create("fixed") {
            storeFile = file("concertcam.jks")
            storePassword = "concertcam"
            keyAlias = "concertcam"
            keyPassword = "concertcam"
        }
    }
    buildTypes {
        getByName("debug") { signingConfig = signingConfigs.getByName("fixed") }
    }
    compileOptions {
        sourceCompatibility = JavaVersion.VERSION_17
        targetCompatibility = JavaVersion.VERSION_17
    }
    kotlinOptions { jvmTarget = "17" }
}
