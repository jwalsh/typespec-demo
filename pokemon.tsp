namespace Pokemon;

/**
 * Possible types of Pokémon.
 */
enum PokeType {
  Normal
  Fire
  Water
  Electric  
  Grass
  Ice
  Fighting
  Poison
  Ground
  Flying
  Psychic
  Bug 
  Rock
  Ghost
  Dragon
  Dark
  Steel
  Fairy
}

/**
 * Represents the defensive effectiveness of a Pokémon against each type.
 * Values are 0 (immune), 0.25 (resistant), 0.5 (resistant), 1 (normal), 2 (weak), 4 (very weak).
 */
model TypeEffectiveness {
  againstNormal: float
  againstFire: float
  againstWater: float
  againstElectric: float
  againstGrass: float
  againstIce: float
  againstFighting: float
  againstPoison: float
  againstGround: float    
  againstFlying: float
  againstPsychic: float
  againstBug: float
  againstRock: float
  againstGhost: float
  againstDragon: float  
  againstDark: float
  againstSteel: float
  againstFairy: float
}

/**
 * Base stats for a Pokémon.
 */
model PokemonStats {
  hp: int
  attack: int
  defense: int  
  specialAttack: int
  specialDefense: int
  speed: int
}

/**
 * Model representing a Pokémon species.
 */
model Pokemon {
  abilities: string[]
  effectiveness: TypeEffectiveness
  stats: PokemonStats  
  eggCycles: int
  baseHappiness: int 
  captureRate: float
  classification: string
  experienceGrowth: int
  height: float  // in meters
  weight: float // in kg
  name: string
  pokedexNumber: int
  percentMale: float
  type1: PokeType
  type2: PokeType
  evolvesFrom: string | null
  evolvesTo: string[] | null
  generation: int
  isLegendary: boolean  
}

interface Pokedex {
  all: Pokemon[]
  getByName(name: string): Pokemon | null
  getByType(type: PokeType): Pokemon[]
  getByGeneration(gen: int): Pokemon[]
  getLegendaries(): Pokemon[]
}
