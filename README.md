# Guild Bank Viewer

A lightweight Guild Bank addon for **World of Warcraft 1.12.x** that allows guild members to browse the inventory of a designated bank character without needing a built-in guild bank.

Instead of relying on spreadsheets, Discord messages, or external websites, Guild Bank Viewer synchronizes the bank alt's inventory directly through the game's Guild AddOn communication channel, making it easy for everyone to see what materials and items are available.

---

## Features

- 📦 Browse a designated guild bank character's inventory from any character.
- 🔄 Automatic synchronization using the Guild AddOn channel.
- ⚡ Lightweight with minimal performance impact.
- 🌐 No external servers, bots, or databases required.
- 🔍 Search items by name.
- 💰 View stack counts and item tooltips.
- 🎮 Designed for World of Warcraft 1.12.x (Vanilla), including private servers such as Turtle WoW and CapyCraft.

---

## How It Works

The addon uses Blizzard's built-in AddOn communication system to share inventory data.

1. Install the addon on the designated guild bank character.
2. Install the addon on any guild members who wish to browse the inventory.
3. When the bank character logs in (or refreshes its inventory), the addon scans all bags.
4. The inventory is synchronized with guild members through the Guild AddOn channel.
5. Guild members can open the Guild Bank Viewer at any time to browse the latest available inventory.

No websites, databases, or additional software are required.

---

## Requirements

- World of Warcraft **1.12.x**
- All guild members who want to receive updates should have the addon installed.
- The designated bank character should log in periodically so everyone has an up-to-date inventory.

---

## Installation

1. Download or clone this repository.
2. Extract the addon into your `Interface/AddOns` folder.

The folder structure should look like:

```
Interface/
└── AddOns/
    └── GuildBankViewer/
```

3. Restart the game or reload your UI.

---

## Usage

### Bank Character

Simply log in with the guild bank character.

The addon will automatically:
- Scan all bags
- Build an inventory database
- Synchronize the data with online guild members

### Guild Members

Open the Guild Bank Viewer window to browse the synchronized inventory.

From there you can:

- Search for items
- View stack quantities
- Hover over items for tooltips
- Check whether the guild bank currently contains an item before asking an officer

---

## Why This Addon?

Guild Bank Viewer provides a simple in-game solution that keeps everyone informed without requiring:
- Discord bots
- Google Sheets
- Websites
- Manual inventory lists

The goal is to make managing guild materials as effortless as possible while staying true to the Vanilla experience.

---

## Contributing

Bug reports, feature requests, and pull requests are always welcome.

If you encounter an issue, please open an Issue describing:
- Your WoW version/server
- Steps to reproduce
- Expected behavior
- Actual behavior

---

## License

This project is licensed under the MIT License. See the `LICENSE` file for details.
