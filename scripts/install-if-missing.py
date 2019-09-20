import json
import os
import subprocess
import sys
from typing import List


class Package:
    def __init__(self, name: str, version: str):
        self.name = name
        self.version = version

    def __str__(self):
        return "{}@{}".format(self.name, self.version)


class Colors:
    RESET = "\033[0m"
    OK = "\033[92m"
    ERROR = "\033[91m"
    WARN = "\033[93m"
    PKG = "\033[96m"
    INFO = "\033[97m\033[44m"


def check_required() -> List[Package]:
    print("{}INFO:{} checking required packages...".format(Colors.INFO, Colors.RESET))
    packages = []
    with open("package.json") as package_file:
        data = json.load(package_file)

        for name, version in data["devDependencies"].items():
            packages.append(Package(name, version.replace("^", "")))

        for name, version in data["dependencies"].items():
            packages.append(Package(name, version.replace("^", "")))

    return packages


def check_installed() -> List[Package]:
    print("{}INFO:{} checking installed packages...".format(Colors.INFO, Colors.RESET))
    packages = []

    proc = None

    if sys.platform.startswith("win"):
        proc = subprocess.run(["cmd", "/C", "npm ls --depth 0 --json"], stdout=subprocess.PIPE)
    elif sys.platform.startswith("linux"):
        proc = subprocess.run(["npm", "ls", "--depth 0", "--json"], stdout=subprocess.PIPE)

    result = proc.stdout.decode("utf-8")

    data = json.loads(result)
    for name, content in data['dependencies'].items():
        packages.append(Package(name, content['version']))

    return packages


def verify(required: List[Package], installed: List[Package]) -> bool:
    result = True

    for pkg in required:
        print("Checking package {}{}{}...".format(Colors.PKG, pkg.name, Colors.RESET), end="")

        installed_package = next((x for x in installed if x.name == pkg.name), None)

        if installed_package:
            if pkg.version == installed_package.version:
                print(" {}installed!{}".format(Colors.OK, Colors.RESET))
            else:
                print(" {}version mismatch! (required: {}, installed: {}){}".format(Colors.WARN, pkg.version,
                                                                                    installed_package.version,
                                                                                    Colors.RESET))
        else:
            print(" {}missing!{}".format(Colors.ERROR, Colors.RESET))
            result = False

    return result


if __name__ == "__main__":
    req = check_required()
    inst = check_installed()

    if verify(req, inst):
        exit(0)
    else:
        exit(1)
