.PHONY: bench bench-android-apk

GRADLE := ../crates/sdk/android/gradlew
EU_ID_ANDROID_SDK ?= $(HOME)/Library/Android/sdk

bench: bench-android-apk

bench-android-apk:
	ANDROID_HOME="$(EU_ID_ANDROID_SDK)" ANDROID_SDK_ROOT="$(EU_ID_ANDROID_SDK)" \
		$(GRADLE) -p EuIdBenchAndroid assembleRelease
