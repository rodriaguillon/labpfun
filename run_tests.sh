#!/bin/bash

# Directorios de entrada y salida
INPUT_DIR="ejemplos/casos"
OUTPUT_DIR="${INPUT_DIR}/salidas"
PROGRAM="./Linter"
LINT_FLAG="-s"

# Iterar sobre los casos del 1 al 24
for i in {1..24}; do
    # Formatear el número del caso con ceros a la izquierda (ej: caso01.mhs)
    CASE_NUM=$(printf "%02d" $i)
    INPUT_FILE="${INPUT_DIR}/caso${CASE_NUM}.mhs"
    EXPECTED_OUTPUT="${OUTPUT_DIR}/caso${CASE_NUM}-sug"
    TEMP_OUTPUT="temp_output.txt"

    echo "Ejecutando test caso${CASE_NUM}..."

    # Ejecutar el programa y redirigir la salida a un archivo temporal
    $PROGRAM $LINT_FLAG $INPUT_FILE > $TEMP_OUTPUT

    # Comparar el resultado con la salida esperada usando diff
    if diff -u "$EXPECTED_OUTPUT" "$TEMP_OUTPUT"; then
        echo "Caso ${CASE_NUM}: ✅ Pasó"
    else
        echo "Caso ${CASE_NUM}: ❌ Falló"
    fi

    # Eliminar el archivo temporal
    rm -f "$TEMP_OUTPUT"
done

echo "Todos los tests completados."
