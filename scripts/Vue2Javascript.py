import re
import os
import glob
import sys

SOURCES_DIR = "../src/"

VUE_EXTENSION = ".vue"
JS_EXTENSION = "_js.js"

def toExternalScriptTag(filename):
  return "<script src=\"./{}\"></script>\n".format(filename)

def splitFile(lines, scriptReplacement):
  contentWithoutJS = ""
  jsContent = ""
  inScript = False
  hadScript = False
  for line in lines:
    if line.startswith("<script>"):
      inScript = True
      hadScript = True
    elif line.startswith("</script>"):
      inScript = False
      contentWithoutJS += scriptReplacement
    else:
      if inScript:
        jsContent += line
      else:
        contentWithoutJS += line


  return contentWithoutJS, jsContent

def extractTwoFiles(file):

  jsFile = os.path.basename(file).replace(VUE_EXTENSION, JS_EXTENSION)
  jsFileLocation = os.path.join(os.path.dirname(file), jsFile)

  if os.path.isfile(jsFileLocation):
    print("Skipping {}, {} already exists".format(file, jsFile))
    return

  print("Converting {} with {}".format(file, jsFile))

  with open(file, encoding="utf8", newline='\n') as fp:
    lines = fp.readlines()

  jsLess, jsContent = splitFile(lines, toExternalScriptTag(jsFile))

  if jsContent == "":
    print("WARNING NO SCRIPT DETECTED IN {}".format(file))
    print("WARNING NO SCRIPT DETECTED IN {}".format(file))
    print("WARNING NO SCRIPT DETECTED IN {}".format(file))
    print("WARNING NO SCRIPT DETECTED IN {}".format(file))
    print("WARNING NO SCRIPT DETECTED IN {}".format(file))

  with open(file, 'w', encoding="utf8", newline='\n') as fp:
    fp.write(jsLess)

  with open(jsFileLocation, 'w', encoding="utf8", newline='\n') as fp:
    fp.write(jsContent)

def mergeFiles(file):
  vueFile = os.path.basename(file).replace(JS_EXTENSION, VUE_EXTENSION)

  print("Merging {} into {}".format(file, vueFile))

  with open(file, 'r', encoding="utf8") as f:
    jsContent = f.read()

  jsContent = "<script>\n" + jsContent + "</script>"

  #print(jsContent)

  vueFileLocation = os.path.join(os.path.dirname(file), vueFile)

  with open(vueFileLocation,'r', encoding="utf8") as f:
    filedata = f.readlines()

  newContent = ""

  for line in filedata:
    if line.startswith("<script src=\""):
      newContent += jsContent + "\n"
    else:
      newContent += line

  with open(vueFileLocation,'w', encoding="utf8", newline='\n') as f:
    f.write(newContent)

  os.remove(file)


def getAllFilesEndingOn(end, search_path):
  files = []

  for x in os.walk(search_path):
    for y in glob.glob(os.path.join(x[0], '*' + end)):
      files.append(y)

  print("Found {} files".format(len(files)))
  return files

def convertVueFiles(sourcePath):
  files = getAllFilesEndingOn(VUE_EXTENSION, sourcePath)

  for file in files:
    extractTwoFiles(file)

def putJSBack(sourcePath):
  files = getAllFilesEndingOn(JS_EXTENSION, sourcePath)

  for file in files:
    mergeFiles(file)

if __name__ == "__main__":
  args = sys.argv

  revert = False
  dir = SOURCES_DIR

  for index, arg in enumerate(args):
    if arg == "revert" or arg == "-r" or arg == "--revert":
       revert = True
    elif index > 0:
       dir = arg

  if revert:
    print("Putting js back in Vue files")
    print("Directory: {}".format(dir))
    putJSBack(dir)
  else:
    print("Extracting js from Vue files")
    print("Directory: {}".format(dir))
    convertVueFiles(SOURCES_DIR)

