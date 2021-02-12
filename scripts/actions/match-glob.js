const glob = require('@actions/glob');
const core = require('@actions/core');
const path = require('path');

// eslint-disable-next-line require-jsdoc
async function main() {
  console.log(process.argv);
  const globs = process.argv.slice(2).join('\n');
  if (globs === '') {
    throw new Error('Must specify some globs!');
  }
  core.info('Reading globs ', globs);
  const globber = await glob.create(globs, {
    followSymbolicLinks: false,
  });
  const files = await globber.glob();

  const file = files.length > 0 ? files[0] : '';

  core.info('Found ' + files.length + ' files');

  core.setOutput('any', files.length > 0);
  core.setOutput('match', file);
  core.setOutput('name', path.basename(file));
  core.setOutput('matchCount', files.length);

  return files.length > 0;
}

main().then((any) => {
  if (!any) {
    core.setFailed(`No files matched!`);
  } else {
    process.exit(0);
  }
}).catch((err) => {
  core.setFailed(`Action failed with error ${err}`);
});

