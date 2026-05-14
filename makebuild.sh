#!/bin/bash

# Verificar que se haya pasado un argumento
if [ -z "$1" ]; then
    echo "Error: Debes proporcionar el número de la sesión a compilar, ej: 1"
    echo "Uso: ./makebuild.sh <numero_sesion>"
    exit 1
fi

SESSION=$1
TARGET_NAME="session$SESSION"

echo "Compilando $TARGET_NAME con Lake..."
lake build "$TARGET_NAME"

if [ $? -eq 0 ]; then
    # El usuario prefiere que los ejecutables de los tests/sesiones se copien a un directorio `build_tests`
    # dentro del directorio de compilación (`.lake/build/`).
    BUILD_TESTS_DIR=".lake/build/build_tests"
    
    if [ ! -d "$BUILD_TESTS_DIR" ]; then
        mkdir -p "$BUILD_TESTS_DIR"
    fi

    # Lake en Windows genera .exe. En Linux/macOS no tienen extensión. Verificamos ambas posibilidades.
    EXE_PATH=".lake/build/bin/$TARGET_NAME"
    if [ -f "${EXE_PATH}.exe" ]; then
        EXE_PATH="${EXE_PATH}.exe"
        TARGET_EXE_NAME="${TARGET_NAME}.exe"
    else
        TARGET_EXE_NAME="$TARGET_NAME"
    fi
    
    if [ -f "$EXE_PATH" ]; then
        cp "$EXE_PATH" "$BUILD_TESTS_DIR/"
        echo "Ejecutable copiado exitosamente a: $BUILD_TESTS_DIR/$TARGET_EXE_NAME"
        echo "Puedes ejecutarlo con: ./$BUILD_TESTS_DIR/$TARGET_EXE_NAME"
    else
        echo "Advertencia: El ejecutable no se encontró en $EXE_PATH o ${EXE_PATH}.exe"
    fi
else
    echo "Error durante la compilación de $TARGET_NAME."
    exit 1
fi
