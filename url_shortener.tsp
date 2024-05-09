namespace URLShortener;

/**
 * A URL object with original and shortened URLs.
 */
model URL {
  originalURL: string
  shortURL: string
}

/**
 * A custom ID type that extends string.
 */ 
scalar URLId extends string

/**
 * Possible errors returned by the API.
 */
enum ErrorCode {
  InvalidURL
  URLNotFound  
}

model ErrorResponse {
  code: ErrorCode
  message: string
}

/**
 * Create a shortened URL.
 */
@server
op shorten(url: string): URL | ErrorResponse

/**
 * Retrieve the original URL from a short URL ID.
 */
@server 
op getOriginalURL(id: URLId): URL | ErrorResponse

/**
 * Defines the interface for implementing URL shortening.
 */
interface Shortener {
  shorten(url: string): URL | ErrorResponse
  getOriginalURL(id: URLId): URL | ErrorResponse
}

/**
 * A basic implementation of the Shortener interface.
 */
@implement(Shortener)
model BasicShortener {
  urls: URL[]

  op shorten(url: string): URL | ErrorResponse {
    // Check if URL is valid
    // Generate short ID 
    // Store mapping and return short URL
  }

  op getOriginalURL(id: URLId): URL | ErrorResponse {
    // Look up ID and return original URL if found
  }
}