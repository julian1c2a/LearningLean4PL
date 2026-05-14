param (
    [Parameter(Mandatory=$true, HelpMessage="Número de la sesión a compilar, ej: 1")]
    [int]$Session
)

$targetName = "session$Session"
Write-Host "Compilando $targetName con Lake..."
lake build $targetName

if ($LASTEXITCODE -eq 0) {
    # El usuario prefiere que los ejecutables de los tests/sesiones se copien a un directorio `build_tests`
    # dentro del directorio de compilación (`.lake/build/`).
    $buildTestsDir = ".lake\build\build_tests"
    
    if (-Not (Test-Path $buildTestsDir)) {
        New-Item -ItemType Directory -Path $buildTestsDir | Out-Null
    }

    $exePath = ".lake\build\bin\$targetName.exe"
    
    if (Test-Path $exePath) {
        Copy-Item $exePath -Destination "$buildTestsDir\" -Force
        Write-Host "Ejecutable copiado exitosamente a: $buildTestsDir\$targetName.exe"
        Write-Host "Puedes ejecutarlo con: .\$buildTestsDir\$targetName.exe"
    } else {
        Write-Host "Advertencia: El ejecutable no se encontró en $exePath"
    }
} else {
    Write-Host "Error durante la compilación de $targetName."
}
