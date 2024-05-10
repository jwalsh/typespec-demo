namespace Recipes;

/**
 * Represents a unit of measurement for ingredient quantities.
 */
enum Unit {
  Tsp
  Tbsp
  Cup
  Oz
  Lb
  Gram
  Kg
  Ml
  L
  Whole
}

/**
 * An ingredient used in a recipe.
 */
model Ingredient {
  item: string
  amount: float
  unit: Unit
}

/**
 * A step in the recipe instructions.
 */
model Step {
  orderIndex: int
  text: string
}

/**
 * A review of a recipe.
 */
model Review {
  author: string
  rating: int [1, 5]
  comment: string
}

/**
 * Represents a recipe in the database.
 */
model Recipe {
  title: string
  description: string
  cuisine: string[]
  ingredients: Ingredient[]
  steps: Step[]
  prepTime: int // in minutes
  cookTime: int // in minutes
  servings: int
  calories: int | null
  images: string[] | null
  reviews: Review[] | null
}

/**
 * Interface to perform recipe database operations.
 */
interface RecipeDatabase {
  /**
   * Get a recipe by its exact title.
   */
  getByTitle(title: string): Recipe | null

  /**
   * Search for recipes matching the given keywords.
   */
  search(query: string): Recipe[]

  /**
   * Find recipes using the specified ingredients.
   */
  findByIngredients(...ingredients: string[]): Recipe[]

  /**
   * Lookup recipes matching the given cuisine.
   */
  findByCuisine(cuisine: string): Recipe[]
  
  /**
   * Get recipes with a maximum prep time.
   */
  findByMaxPrepTime(minutes: int): Recipe[]

  /**
   * Find recipes with a minimum average rating.
   */
  findByMinRating(rating: int): Recipe[]
}
