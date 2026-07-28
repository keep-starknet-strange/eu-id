.PHONY: bench bench-android-apk

EU_ID_ANDROID_SDK ?= $(HOME)/Library/Android/sdk

bench: bench-android-apk

bench-android-apk:
	EU_ID_ANDROID_SDK="$(EU_ID_ANDROID_SDK)" bash ./build-bench-android.sh
