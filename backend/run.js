import 'dotenv/config'
import { createHash, hkdfSync, randomBytes } from 'node:crypto'
import { mkdirSync, writeFileSync, readFileSync } from 'node:fs'
import { ethers } from 'ethers'

const chainId = parseInt(process.env.CHAIN) || 1

// ERC-2333

const sha256 = (m) => createHash('sha256').update(m).digest()
const r = 52435875175126190479447740508185965837690552500527637822603658699938581184513n

function OS2IP(a) {
  let result = 0n
  let m = 1n
  for (const x of a.toReversed()) {
    result += BigInt(x) * m
    m *= 256n
  }
  return result
}

function I2OSP(n, l) {
  const result = new Uint8Array(l)
  while (l) {
    result[--l] = parseInt(n % 256n)
    n /= 256n
  }
  return result
}

const L = 48
const L2 = Uint8Array.from([0, L])
function secretKeyFromSeed(seed) {
  const seed0 = new Uint8Array(seed.length + 1)
  seed0.set(seed)
  let salt = "BLS-SIG-KEYGEN-SALT-"
  let SK = 0n
  while (SK == 0n) {
    salt = sha256(salt)
    const OKM = new Uint8Array(hkdfSync('sha256', seed0, salt, L2, L))
    SK = OS2IP(OKM) % r
  }
  return SK
}

function lamportFromParent(sk, index) {
  const salt = I2OSP(BigInt(index), 4)
  const IKM = I2OSP(sk, 32)
  const lamport = []
  lamport.push(hkdfSync('sha256', IKM, salt, '', 32 * 255))
  const not_IKM = IKM.map(b => ~b)
  lamport.push(hkdfSync('sha256', not_IKM, salt, '', 32 * 255))
  const lamport_PK = new Uint8Array(2 * 32 * 255)
  for (const j of [0, 1]) {
    for (const i of Array(255).keys()) {
      const lamport_ji = new Uint8Array(lamport[j], i * 32, 32)
      lamport_PK.set(sha256(lamport_ji), (j * 255 + i) * 32)
    }
  }
  return sha256(lamport_PK)
}

const deriveChild = (sk, index) =>
  secretKeyFromSeed(lamportFromParent(sk, index))

// addresses are checksummed (ERC-55) hexstrings with the 0x prefix
// pubkeys are lowercase hexstrings with the 0x prefix
// timestamps are integers representing seconds since UNIX epoch
// contents are utf8 encoded unless otherwise specified
//
// filesystem database layout:
// db/${chainId}/${address}/init : timestamp
// db/${chainId}/${address}/seed : 32 bytes (no encoding)
// db/${chainId}/${address}/${pubkey}/log : JSON lines of log entries
//
// the log is an append-only record of user actions
// log entries have this format:
// { type: "setFeeRecipient" | "setGraffiti" | "setEnabled" | "exit"
// , time: timestamp
// , data: address | string | bool | undefined
// }
//
// environment variables
// CHAIN
// COMMAND
// ADDRESS
// PUBKEY
// DATA

const commands = ["init", "deposit", "setFeeRecipient", "setGraffiti", "setEnabled", "exit", "test"]

if (!commands.includes(process.env.COMMAND)) {
  console.error(`Unrecognised command ${process.env.COMMAND}: should be one of ${commands}.`)
  process.exit(1)
}

if (process.env.COMMAND == 'test') {
  const testCases = [
    {
      seed: '0xc55257c360c07c72029aebc1b53c05ed0362ada38ead3e3e9efa3708e53495531f09a6987599d18264c1e1c92f2cf141630c7a3c4ab7c81b2f001698e7463b04',
      master_SK: 6083874454709270928345386274498605044986640685124978867557563392430687146096n,
      child_index: 0,
      child_SK: 20397789859736650942317412262472558107875392172444076792671091975210932703118n
    },
    {
      seed: '0x3141592653589793238462643383279502884197169399375105820974944592',
      master_SK: 29757020647961307431480504535336562678282505419141012933316116377660817309383n,
      child_index: 3141592653,
      child_SK: 25457201688850691947727629385191704516744796114925897962676248250929345014287n
    },
    {
      seed: '0x0099FF991111002299DD7744EE3355BBDD8844115566CC55663355668888CC00',
      master_SK: 27580842291869792442942448775674722299803720648445448686099262467207037398656n,
      child_index: 4294967295,
      child_SK: 29358610794459428860402234341874281240803786294062035874021252734817515685787n
    },
    {
      seed: '0xd4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3',
      master_SK: 19022158461524446591288038168518313374041767046816487870552872741050760015818n,
      child_index: 42,
      child_SK: 31372231650479070279774297061823572166496564838472787488249775572789064611981n
    }
  ]
  for (const [i, {seed, master_SK, child_index, child_SK}] of testCases.entries()) {
    const seedBytes = ethers.getBytes(seed)
    const sk = secretKeyFromSeed(seedBytes)
    const csk = deriveChild(sk, child_index)
    if (sk == master_SK) {
      if (csk == child_SK)
        console.log(`Test case ${i} passed`)
      else {
        console.error(`Test case ${i} failed: Got ${csk} instead of ${child_SK}`)
        process.exit(1)
      }
    }
    else {
      console.error(`Test case ${i} failed: Got ${sk} instead of ${master_SK}`)
      process.exit(1)
    }
  }
  process.exit()
}

const address = ethers.getAddress(process.env.ADDRESS)

if (process.env.COMMAND == 'init') {
  const dirPath = `db/${chainId}/${address}`
  mkdirSync(dirPath, {recursive: true})
  const timestamp = Math.floor(Date.now() / 1000)
  writeFileSync(`${dirPath}/init`, timestamp.toString(), {flag: 'wx'})
  writeFileSync(`${dirPath}/seed`, randomBytes(32), {flag: 'wx'})
  process.exit()
}

else if (process.env.COMMAND == 'deposit') {
  const dirPath = `db/${chainId}/${address}`
  const seed = new Uint8Array(readFileSync(`${dirPath}/seed`))
  const sk = secretKeyFromSeed(seed)

  console.error(`Not implemented yet: ${process.env.COMMAND}`)
  process.exit(1)
}

else {
  console.error(`Not implemented yet: ${process.env.COMMAND}`)
  process.exit(1)
}
