#!/bin/bash

export MLSDK=${MLSDK:-/mnt/c/Users/avaer/MagicLeap/mlsdk/v0.18.0}

"$MLSDK/tools/mldb/mldb.exe" -d install -u build/magicleap/app-device/app-device.mpk
