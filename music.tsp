namespace MusicLibrary;

/**
 * Represents a musical artist or band.
 */
model Artist {
  name: string
  genre: string[]
  origin: string | null
  members: string[] | null
  formedYear: int | null
  bio: string | null
  images: string[] | null
}

/**
 * An album released by an artist.
 */
model Album {
  title: string
  artist: Artist
  releaseYear: int
  genre: string[]
  tracks: Track[]
  coverArt: string | null
}

/**
 * A single track or song.
 */
model Track {
  title: string
  artist: Artist
  album: Album | null
  duration: int // in seconds
  genre: string[]
  lyrics: string | null
  composer: string | null
}

/**
 * A user-created playlist containing tracks.
 */
model Playlist {
  name: string
  owner: string
  tracks: PlaylistTrack[]
}

/**
 * Represents a track within a playlist, including its order.
 */
model PlaylistTrack {
  track: Track
  orderIndex: int
}

/**
 * Interface to manage and query the music library.
 */
interface MusicLibraryManager {
  /**
   * Add a new artist to the library.
   */
  addArtist(artist: Artist): void

  /**
   * Add an album to an artist's discography.
   */
  addAlbum(artistName: string, album: Album): void

  /**
   * Create a new user playlist.
   */
  createPlaylist(name: string, owner: string): Playlist

  /**
   * Add a track to a playlist.
   */
  addTrackToPlaylist(playlistName: string, track: Track): void

  /**
   * Get an artist by their exact name.
   */
  getArtistByName(name: string): Artist | null

  /**
   * Find artists matching a name substring.
   */  
  searchArtists(query: string): Artist[]

  /**
   * Lookup an album by its exact title.
   */
  getAlbumByTitle(title: string): Album | null

  /**
   * Get all albums released in a given year.
   */
  getAlbumsByYear(year: int): Album[]

  /**
   * Find tracks matching a title substring.
   */
  searchTracks(query: string): Track[]
  
  /**
   * Get tracks longer than a specified duration.
   */
  getTracksLongerThan(seconds: int): Track[]

  /**
   * Find playlists with a matching name.
   */
  searchPlaylists(query: string): Playlist[]

  /**
   * Get the tracks in a playlist.
   */
  getPlaylistTracks(playlistName: string): Track[] 
}
