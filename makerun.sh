#!/bin/bash

if [ -z "$1" ]; then
    echo "Error: Debes proporcionar el número de la sesión a ejecutar, ej: 1"
    echo "Uso: ./makerun.sh <numero_sesion>"
    exit 1
fi

SESSION=$1
TARGET_NAME="session$SESSION"
BUILD_TESTS_DIR=".lake/build/build_tests"

EXE_PATH="$BUILD_TESTS_DIR/$TARGET_NAME"

# Verificamos si existe la versión con .exe (Windows) o sin extensión (Linux/Mac)
if [ -f "${EXE_PATH}.exe" ]; then
    EXE_PATH="${EXE_PATH}.exe"
fi

if [ -f "$EXE_PATH" ]; then
    echo -e "\033[32m=== Ejecutando $TARGET_NAME ===\033[0m"
    "./$EXE_PATH"
else
    echo -e "\033[31mError: No se encontró el ejecutable en $BUILD_TESTS_DIR\033[0m"
    echo -e "\033[33mAsegúrate de compilarlo primero ejecutando: ./makebuild.sh $SESSION\033[0m"
    exit 1
fi
