# REQUIRES -Version 3.0

param(
    [switch]$strict = $false
)

<#
.SYNOPSIS
    Parses objects structured in a @{x = y} format and returns them in a @{Key = x, Value = y} format.
#>
function Get-ObjectMembers
{
    [CmdletBinding()]
    Param(
        [Parameter(Mandatory = $True, ValueFromPipeline = $True)]
        [PSCustomObject]$obj
    )
    $obj | Get-Member -MemberType NoteProperty | ForEach-Object {
        $key = $_.Name
        [PSCustomObject]@{ Key = $key; Value = $obj."$key" }
    }
}

# Read required packages from package.json file.
Write-Host 'INFO:' -NoNewline -ForegroundColor White -BackgroundColor Cyan
Write-Host ' checking required packages...'

$required = @()

$packageFile = Get-Content 'package.json' | Out-String | ConvertFrom-Json

$packageFile.dependencies[0] | Get-ObjectMembers | ForEach-Object {
    $required += ,[PSCustomObject]@{ Package = $_.Key; Version = $_.Value -replace '[\^]', '' }
}

$packageFile.devDependencies[0] | Get-ObjectMembers | ForEach-Object {
    $required += ,[PSCustomObject]@{ Package = $_.Key; Version = $_.Value -replace '[\^]', '' }
}

# Query NPM for installed packages.
Write-Host 'INFO:' -NoNewline -ForegroundColor White -BackgroundColor Cyan
Write-Host ' checking installed packages...'

$installed = @()

$npmList = (& npm list --json --depth 0 2> $null) | ConvertFrom-Json
$npmList.dependencies | Get-ObjectMembers | ForEach-Object {
    $installed += ,[PSCustomObject]@{ Package = $_.Key; Version = $_.Value.version }
}

# Compare installed and required packages.
Write-Host 'INFO:' -NoNewline -ForegroundColor White -BackgroundColor Cyan
Write-Host ' checking installed packages...'

$install = $false

$required | ForEach-Object {
    Write-Host 'Checking package ' -NoNewline -ForegroundColor White
    Write-Host $_.Package -NoNewline -ForegroundColor Cyan
    Write-Host '... ' -NoNewline -ForegroundColor White

    If ( $installed.Package.Contains($_.Package))
    {
        # Package is installed, check if versions match.
        $version = $installed | Where-Object Package -eq $_.Package | Select-Object -Expand Version
        If ($version -eq $_.Version)
        {
            Write-Host 'installed!' -ForegroundColor DarkGreen
        }
        Else
        {
            Write-Host "version mismatch! (installed: $version, required: $( $_.Version ))" -ForegroundColor Yellow
            if ($strict)
            {
                $install = $true
            }
        }
    }
    Else
    {
        Write-Host 'missing!' -ForegroundColor Red
        $install = $true
    }
}

if ($install)
{
    Write-Host 'INFO:' -NoNewline -ForegroundColor White -BackgroundColor Cyan
    Write-Host ' installing packages'
    npm install
}
