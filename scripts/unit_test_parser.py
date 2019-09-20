import json

def tex_escape(text):
    return text.replace("&", "\\&").replace("$", "\\$").replace("_", "\\_")

def append_test(file, suites):
  for suite in suites:
    for test in suite["tests"]:
      text = "\\item " + tex_escape(test["fullTitle"]) + "\n"
      file.write(text)
    append_test(file, suite["suites"])

def main():
  tex_file = open("unit_tests.tex", "w", encoding="utf8")

  with open("../out/test-unit/index.json", "r", encoding="utf8") as json_file:
    data = json.load(json_file)
    append_test(tex_file, data["results"])

  print("Done!")
  tex_file.close()

if __name__ == '__main__':
    main()
