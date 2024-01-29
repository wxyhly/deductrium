const dict = {
    '"nodes":[{"type":"replvar"': "%:",
    '{"type":"replvar","name":"': "*:",
    '"nodes":[]': "o:",
    '"value":{': "v:",
    '"nodes":[{': "d:",
    '"replaceNames":["$0","$1","$2"': "9:",
    '"replaceNames":["$0","$1"': "8:",
    '"replaceNames":["$0"': "7:",
    '"replaceNames":[': "#:",
    '"conditionIdxs":[': "Y:",
    '"replaceValues":[': "$:",
    '"deductionIdx":"': "N:",
    '"conditions":[': "c:",
    '"conclusion":{': "j:",
    '"conclusion":': ",:",
    '"from":"': "f:",
    '"name":"#array"': "a:",
    '"type":"fn"': "k:",
    '"type":"meta"': "m:",
    '"type":"replvar"': "r:",
    '"type":"sym"': "s:",
    '"type":': "t:",
    '"name":"$0"': "0:",
    '"name":"$1"': "1:",
    '"name":"$2"': "2:",
    '"name":">"': "x:",
    '"name":"~"': "~:",
    '"name":': "n:",
    'n:"#0"': "):",
    'n:"⊢"': "T:",
    'n:"V"': "V:",
    '}]}': "b:",
    '},{': "q:",
    ':},': "::",
    's:,x:,': "z:",
    'q:z:,': "Z:",
    'z:d:s:,': "D:",
    'k:,n:"#replace",%:': "R:",
    'k:,n:"#satisfy",%:,': "S:",
    '*:$2"b:]': "B:",
    ':*:$': "X:",
    'b:]},': "A:",
    '"}],#:': "C:",
    'f:一阶逻辑"': "P:",
    'f:m0所需宏"': "/:",
    'f:*录制宏"': "Q:",
    'f:符号宏"': "W:",
    'f:命题逻辑"': "G:",
    ':],': "I:",
    '`': "(:",
    ':,': "`",
    'Q`"steps":[{Y': "^:",
    'v:m`T`d:k`a`': "!:",
    'V`%`0:': "?:",
    '.': ";:",
    ':q:': ".",
};
const replaceArr1 = Object.entries(dict);
const replaceArr2 = replaceArr1.slice(0).reverse();
export class SavesParser{
    
    serialize(json:string){
        for(const [a,b] of replaceArr1){
            json = json.replaceAll(a,b);
        }
        return json;
    }
    deserialize(str:string){
        for(const [a,b] of replaceArr2){
            str = str.replaceAll(b,a);
        }
        return str;
    }
}