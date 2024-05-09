namespace Moria;

/**
 * Base model for all items.
 */
model Item {
  name: string
  level: int
  cost: int
}

/**
 * Possible types of food.
 */
enum FoodType {
  Ration
  Pint
  Mushroom
  Biscuit  
  Waybread
  Jerky
  Slime
}

/**
 * Food items that can be consumed.
 */
model Food extends Item {
  type: FoodType  
  nutrition: int
}

/**
 * Amulet item that can be worn.
 */
model Amulet extends Item {
  minBonus?: int
  maxBonus?: int
  costPerBonus?: int
}

/**
 * Possible types of armor.
 */
enum ArmorType {  
  Body
  Shield
  Cloak
  Helm
  Gloves
  Boots
}

/**
 * Armor item that can be worn.
 */
model Armor extends Item {
  type: ArmorType
  weight: float  
  ac: int
  minHit?: int
}

/**
 * Weapon item that can be wielded.
 */
model Weapon extends Item {
  weight: float
  damage: string
}

/**
 * Possible types of missile weapons.
 */
enum MissileType {
  Arrow
  Bolt  
}

/**
 * Ammunition for missile weapons
 */
model Missile extends Item {
  type: MissileType
  damage: string  
  costPerBonus: int
}

/**
 * Various magical items.
 */
model MagicItem extends Item {}

model Ring extends MagicItem {
  minBonus?: int
  maxBonus?: int  
  costPerBonus?: int
}

model Staff extends MagicItem {
  minCharges: int
  maxCharges: int
}

model Wand extends MagicItem {
  minCharges: int
  maxCharges: int
}

model Scroll extends MagicItem {}

model Potion extends MagicItem {
  nutrition?: int
}

/**
 * Possible types of gems.
 */
enum GemType {
  Opal  
  Sapphire
  Ruby
  Diamond
  Emerald  
}

/**
 * Gems and valuables.
 */
model Valuable extends Item {
  type?: GemType  
}

/**
 * Defines the items available in the game.
 */
interface ItemLibrary {  
  food: Food[]
  amulets: Amulet[]
  armor: Armor[]
  weapons: Weapon[]
  missiles: Missile[]
  rings: Ring[]
  staves: Staff[]  
  wands: Wand[]
  scrolls: Scroll[]
  potions: Potion[]
  valuables: Valuable[]
}
