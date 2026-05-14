param (
    [Parameter(Mandatory=$true, HelpMessage="Número de la sesión a ejecutar, ej: 1")]
    [int]$Session
)

$targetName = "session$Session"
$exePath = ".lake\build\build_tests\$targetName.exe"

if (Test-Path $exePath) {
    Write-Host "=== Ejecutando $targetName ===" -ForegroundColor Green
    & ".\$exePath"
} else {
    Write-Host "Error: No se encontró el ejecutable $exePath" -ForegroundColor Red
    Write-Host "Asegúrate de compilarlo primero ejecutando: .\makebuild.ps1 $Session" -ForegroundColor Yellow
}
