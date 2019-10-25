import readFile from './readfile';

const fs = require('fs');
const filePath = '../../wrapper/assistance/symbols.json';

/**
 * Function for adding content to a json file
 * @param {Object} newSymbol the symbol to add
 */
function addSymbol(newSymbol) {
  console.log(newSymbol);
  // readFile(file, (result) => {
  //   const symbolList = JSON.parse(result);
  //   symbolList[5].elements.push(newSymbol);
  //   const jsonSymbolList = JSON.stringify(symbolList);
  //   fs.writeFile(file, jsonSymbolList, (err) => {
  //     if (err) throw err;
  //     console.log('Replaced');
  //   });
  // });
}

export default addSymbol;
