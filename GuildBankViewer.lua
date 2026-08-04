-- Guild Bank Viewer
-- Works on Vanilla 1.12.1 clients (Turtle WoW / CapyCraft).
--
-- Features:
--   * Bank alt(s) auto-sync their bags+bank+gold to the whole guild over the
--     guild addon channel whenever their bank window opens/closes/changes.
--   * Any guild member with the addon can browse/search that data with /gbank.
--   * Members can request items; officers see a ticket queue and can
--     approve/deny requests with /gbank tickets.
--   * The bank alt doesn't need to be online for the data to be useful.
--     Every client that has ever received a bank sync keeps its own cached
--     copy (SavedVariables persist across sessions). If someone logs in and
--     asks for a sync (SYNCREQ) but no bank alt answers within a few
--     seconds, any other online member who has cached data for that alt
--     will relay it (RSYNC) on the alt's behalf, tagged as "cached" data
--     with the timestamp it's actually from. A live sync from the real
--     bank alt always wins over a relay if/when one shows up.
--
-- Nothing leaves the game client. No Discord, no external bot, no website.

local ADDON_PREFIX = "GBANKV1"
local CHUNK_SIZE = 200
local SEND_INTERVAL = 0.25 -- seconds between queued message sends

GuildBankViewerDB = GuildBankViewerDB or {}         -- account-wide: bank data + tickets
GuildBankViewerCharDB = GuildBankViewerCharDB or {} -- per-character: bank alt / officer flags

GuildBankViewerDB.banks = GuildBankViewerDB.banks or {}
-- GuildBankViewerDB.banks[altName] = { items = {[itemID]=count}, gold = copper, lastUpdate = time, label = altName }

GuildBankViewerDB.tickets = GuildBankViewerDB.tickets or {}
-- GuildBankViewerDB.tickets[ticketID] = { itemID, itemName, qty, altName, requester, status, ts }

GuildBankViewerDB.listings = GuildBankViewerDB.listings or {}
-- GuildBankViewerDB.listings[listingID] = { itemID, itemName, qty, price(copper), seller, ts }

GuildBankViewerDB.bounties = GuildBankViewerDB.bounties or {}
-- GuildBankViewerDB.bounties[bountyID] = { itemID, itemName, qty, reward(copper), poster, ts }

local frame = CreateFrame("Frame", "GuildBankViewerEventFrame")
local sendQueue = {}
local sendTimer = 0
local lastBroadcastSignature = nil
local hasSentSyncRequest = false
local lastSyncReqResponse = 0
local lastMarketReqResponse = 0
local SYNC_REQ_COOLDOWN = 30 -- seconds; avoid a flood if several people log in around the same time

-- Set (to GetTime() + delay) whenever a bank-frame event suggests it's time
-- to rescan; actually acted on from OnUpdate once that time passes. See the
-- BANKFRAME_OPENED handling below for why this is delayed rather than
-- instant.
local pendingBankScanAt = nil

-- Relay support: if the real bank alt is offline, another online member who
-- has cached bank data can resend it on the alt's behalf. See the SYNCREQ
-- handler and the pendingRelayChecks queue below.
local lastSyncActivityAt = {}  -- lastSyncActivityAt[altName] = time() of the last SYNC or RSYNC seen for that alt
local lastRelayedAt = {}       -- lastRelayedAt[altName] = time() we last relayed data for that alt (self-throttle)
local pendingRelayChecks = {}  -- { {altName=, fireAt=, reqTime=}, ... }
local RELAY_MIN_DELAY = 3      -- seconds to wait after a SYNCREQ before considering a relay
local RELAY_MAX_JITTER = 4     -- extra random seconds, spread out so not everyone relays at once
local RELAY_SELF_COOLDOWN = 30 -- don't relay the same alt again this soon after we last did

-- Forward-declared: the real body is assigned further down, after
-- QueueChunks/BuildSyncPayload exist, but OnUpdate is wired up before that.
-- Declaring the local here (rather than letting OnUpdate reference an
-- as-yet-undeclared name) ensures OnUpdate's closure captures this actual
-- local as an upvalue instead of silently falling back to a global.
local ProcessPendingRelays
local BroadcastBankData

----------------------------------------------------------------------
-- Utility
----------------------------------------------------------------------

local function Print(msg)
    DEFAULT_CHAT_FRAME:AddMessage("|cff33ff99[GuildBank]|r " .. msg)
end

-- Strip characters that can break other addons' chat/addon-message handling
-- when our text passes through a shared library (e.g. "%" has caused errors
-- in some ChatThrottleLib versions used by other addons like Aux).
local function SanitizeText(str)
    if not str then return str end
    str = string.gsub(str, "%%", "")
    str = string.gsub(str, "|", "")
    return str
end

local function GetItemIDFromLink(link)
    if not link then return nil end
    local _, _, idStr = string.find(link, "item:(%d+)")
    if idStr then return tonumber(idStr) end
    return nil
end

-- This server's item strings are "item:itemID:enchant:suffixID:uniqueID"
-- -- shorter than the 8-field jewel/socket format real vanilla clients
-- with gems would use (Turtle has no item sockets, so those fields are
-- simply absent here). Confirmed against real dumped links via /gbank
-- links: "item:10504:0:1422:0" = Green Lens of Fire Resistance,
-- "item:10504:0:1975:0" = of Frozen Wrath, "item:10504:0:1468:0" = of
-- Shadow Resistance -- same itemID (10504), only the 3rd field differs,
-- and it's what drives the suffix text. A non-suffixed item like Pattern:
-- Robe of the Void dumped as "item:14514:0:0:0" -- suffix field 0, as
-- expected. Reading only the itemID (as GetItemIDFromLink does) throws
-- that distinction away, which is what was merging different-suffix items
-- into one summed/misnamed row instead of counting them separately.
local function GetItemIDAndSuffixFromLink(link)
    if not link then return nil, 0 end
    local _, _, idStr, suffixStr = string.find(
        link, "item:(%d+):%-?%d+:(%-?%d+):"
    )
    if idStr then
        return tonumber(idStr), tonumber(suffixStr) or 0
    end
    -- Malformed/partial link -- fall back to itemID-only rather than
    -- dropping the item entirely.
    return GetItemIDFromLink(link), 0
end

-- Stable key for "this itemID with this random suffix" so items table
-- lookups/aggregation never conflate two different suffixes.
local function ItemKey(itemID, suffixID)
    return itemID .. ":" .. (suffixID or 0)
end

-- Rebuilds a minimal item link from an itemID + suffixID so GetItemInfo /
-- GetItemIcon / tooltips resolve the correctly suffixed name and stats
-- instead of the bare base-item name. Matches the 4-field format above.
local function BuildItemLink(itemID, suffixID)
    return "item:" .. itemID .. ":0:" .. (suffixID or 0) .. ":0"
end

----------------------------------------------------------------------
-- Known-item database (for the New Listing / New Bounty search box)
--
-- Vanilla has no "search all items in the game" API, and a hand-typed
-- list of item IDs risks being wrong -- especially on a custom server
-- where IDs can differ from retail Classic. Instead, this passively
-- learns every item the client ever actually resolves: hovering a
-- tooltip anywhere, browsing your bags, opening the Bank tab, etc. all
-- feed it. Once an item's been seen once by anyone, it's searchable
-- from then on, and the data is always exactly what the server sent --
-- never guessed.
----------------------------------------------------------------------

GuildBankViewerDB.knownItems = GuildBankViewerDB.knownItems or {} -- knownItems[itemID] = name

local function LearnItem(itemID, name)
    if itemID and name and name ~= "" then
        GuildBankViewerDB.knownItems[itemID] = name
    end
end

local origGetItemInfo = GetItemInfo
GetItemInfo = function(item)
    -- Named per Turtle WoW's actual return order, which has no
    -- itemStackCount field (see SafeGetItemIcon below) -- equipSlot and
    -- texture were previously mislabeled one slot too late here.
    local name, link, quality, iLevel, reqLevel, class, subclass, equipSlot, texture = origGetItemInfo(item)
    if name then
        local id = tonumber(item) or GetItemIDFromLink(item) or GetItemIDFromLink(link)
        LearnItem(id, name)
    end
    return name, link, quality, iLevel, reqLevel, class, subclass, equipSlot, texture
end

-- GetItemIcon isn't guaranteed to exist as a global on every server/client
-- -- some builds simply don't implement it, and calling a nonexistent
-- global errors immediately and aborts whatever function called it (which
-- is what was leaving the list blank on clients without it: the very
-- first row's icon lookup threw and stopped GuildBankViewer_RefreshList
-- before it filled in anything).
--
-- Where GetItemIcon *does* exist, it's the reliable source. Some servers'
-- GetItemInfo implementations don't return a texture in the same return
-- slot Blizzard's client does (or don't return one at all), so blindly
-- trusting "the 10th return value" there can hand back some unrelated
-- number (sell price, level, etc.) instead of a texture path -- and
-- SetTexture() with a number is silently interpreted as an RGB color
-- rather than erroring, which is what was painting every icon solid red
-- instead of failing loudly. Validating the type before trusting either
-- source avoids that either way.
local ICON_PLACEHOLDER = "Interface\\Icons\\INV_Misc_QuestionMark"

local function SafeGetItemIcon(item)
    if type(GetItemIcon) == "function" then
        local ok, texture = pcall(GetItemIcon, item)
        if ok and type(texture) == "string" and texture ~= "" then
            return texture
        end
    end
    -- Turtle WoW's server doesn't return itemStackCount from GetItemInfo
    -- (confirmed on the Turtle forums -- stack size just isn't available
    -- from it there), which shifts every field after it one slot earlier
    -- than the standard Blizzard signature. So on Turtle, texture is the
    -- 9th return value, not the 10th. AtlasLoot's Turtle fork reads it at
    -- the same 9th position, which is what confirmed this. Getting this
    -- wrong is exactly what silently left every icon on the placeholder
    -- for anyone without ClassicAPI (GetItemIcon exists as its own
    -- function and never went through this positional parsing at all,
    -- which is why installing ClassicAPI appeared to "fix" icons -- it
    -- was actually just bypassing this bug, not working around a real
    -- data gap).
    local _, _, _, _, _, _, _, _, texture = GetItemInfo(item)
    if type(texture) == "string" and texture ~= "" then
        return texture
    end
    return nil
end

-- Guard for anywhere a texture is about to be handed to Texture:SetTexture
-- -- returns the placeholder icon instead of whatever was passed in unless
-- it's actually a usable non-empty string.
local function SafeIconTexture(texture)
    if type(texture) == "string" and texture ~= "" then
        return texture
    end
    return ICON_PLACEHOLDER
end

local function FormatMoney(copper)
    copper = copper or 0
    local gold = math.floor(copper / 10000)
    local silver = math.floor(mod(copper, 10000) / 100)
    local cop = mod(copper, 100)
    if gold > 0 then
        return gold .. "g " .. silver .. "s " .. cop .. "c"
    elseif silver > 0 then
        return silver .. "s " .. cop .. "c"
    else
        return cop .. "c"
    end
end

----------------------------------------------------------------------
-- Guild roster / officer verification
--
-- "Officer" is NOT a checkbox anyone can tick on themselves. It's derived
-- from each player's real guild rank, pulled straight from the server via
-- GuildRoster()/GetGuildRosterInfo(). A player can't fake their own rank,
-- and incoming approve/deny messages are checked against the message's
-- actual sender (from the addon-channel event, which the game itself
-- stamps and which an addon cannot spoof) -- not against any name or
-- claim embedded in the message text.
----------------------------------------------------------------------

local guildRankOf = {} -- guildRankOf[charName] = { index = rankIndex, title = rankTitle }

local function RefreshGuildRoster()
    if IsInGuild() then
        GuildRoster()
    end
end

local function RebuildRosterCache()
    guildRankOf = {}
    local total = GetNumGuildMembers and GetNumGuildMembers() or 0
    for i = 1, total do
        local name, rankTitle, rankIndex = GetGuildRosterInfo(i)
        if name then
            guildRankOf[name] = { index = rankIndex, title = rankTitle }
        end
    end
end

local function GetOfficerThreshold()
    return GuildBankViewerDB.officerRankThreshold or 1
end

-- Is `name` (a real character name) currently an officer, per their actual
-- guild rank and the locally configured cutoff?
local function IsOfficer(name)
    local info = guildRankOf[name]
    if not info then return false end
    return info.index <= GetOfficerThreshold()
end

----------------------------------------------------------------------
-- Guild scoping
--
-- GuildBankViewerDB (banks/listings/bounties/tickets) is account-wide, not
-- per-character -- that's what lets alts in the SAME guild share cached
-- data across sessions. But it means a brand new character, or an alt in a
-- totally different guild, would otherwise see whatever the last-synced
-- guild's data was too. Every record gets tagged with the guild it was
-- current for when it was written, and every place that displays or
-- relays that data filters down to whatever guild the ACTIVE character is
-- in right now.
----------------------------------------------------------------------

local function CurrentGuildKey()
    if not IsInGuild() then return nil end
    local guildName = GetGuildInfo("player")
    if not guildName or guildName == "" then return nil end
    return (GetRealmName() or "") .. "-" .. guildName
end

-- Serialize a { [itemID] = count } table into "id:count;id:count;..."
-- items is keyed by "itemID:suffixID" (see ItemKey) -- each key already
-- contains both numbers, so serializing just tacks the count on.
local function SerializeItems(items)
    local parts = {}
    for key, count in pairs(items) do
        table.insert(parts, key .. ":" .. count)
    end
    return table.concat(parts, ";")
end

local function DeserializeItems(str)
    local items = {}
    for pair in string.gfind(str, "[^;]+") do
        local _, _, id, suffix, count = string.find(pair, "^(%-?%d+):(%-?%d+):(%d+)$")
        if id then
            items[id .. ":" .. suffix] = tonumber(count)
        else
            -- Pre-suffix-aware cached data was just "itemID:count" -- read
            -- it as suffix 0 instead of silently discarding it.
            local _, _, oldID, oldCount = string.find(pair, "^(%d+):(%d+)$")
            if oldID then
                items[oldID .. ":0"] = tonumber(oldCount)
            end
        end
    end
    return items
end

-- Full sync payload = "<ts>~<gold>~<itemsSerialized>"
-- `ts` is when the data was actually scanned (the bank alt's own clock),
-- not when a receiver downloads it -- that's what lets a relay forward
-- someone else's data while still being honest about how old it is.
local function BuildSyncPayload(items, gold, ts)
    ts = ts or time()
    return ts .. "~" .. gold .. "~" .. SerializeItems(items)
end

local function ParseSyncPayload(full)
    local _, _, tsStr, goldStr, itemsStr = string.find(full, "^(%d+)~(%d+)~(.*)$")
    local ts = tonumber(tsStr) or time()
    local gold = tonumber(goldStr) or 0
    local items = DeserializeItems(itemsStr or "")
    return ts, gold, items
end

----------------------------------------------------------------------
-- Scanning (runs on whichever character is flagged as a bank alt)
----------------------------------------------------------------------

local function ScanBagsAndBank()
    local items = {}

    local function scanContainer(bagID)
        local slots = GetContainerNumSlots(bagID)
        if not slots or slots == 0 then return end
        for slot = 1, slots do
            local link = GetContainerItemLink(bagID, slot)
            if link then
                local _, count = GetContainerItemInfo(bagID, slot)
                count = count or 1
                local itemID, suffixID = GetItemIDAndSuffixFromLink(link)
                if itemID then
                    local key = ItemKey(itemID, suffixID)
                    items[key] = (items[key] or 0) + count
                end
            end
        end
    end

    for bagID = 0, 4 do
        scanContainer(bagID)
    end

    scanContainer(-1)
    for bagID = 5, 10 do
        scanContainer(bagID)
    end

    return items
end

----------------------------------------------------------------------
-- Sending queue (throttled so we don't flood the addon channel)
----------------------------------------------------------------------

local function QueueMessage(msg)
    table.insert(sendQueue, msg)
end

frame:SetScript("OnUpdate", function()
    if table.getn(pendingRelayChecks) > 0 and ProcessPendingRelays then
        ProcessPendingRelays()
    end

    if pendingBankScanAt and GetTime() >= pendingBankScanAt and BroadcastBankData then
        pendingBankScanAt = nil
        BroadcastBankData()
    end

    if table.getn(sendQueue) == 0 then return end
    sendTimer = sendTimer + arg1
    if sendTimer < SEND_INTERVAL then return end
    sendTimer = 0

    local msg = table.remove(sendQueue, 1)
    SendAddonMessage(ADDON_PREFIX, msg, "GUILD")
end)

----------------------------------------------------------------------
-- Broadcasting bank data (bank alt -> guild)
----------------------------------------------------------------------

local function QueueChunks(msgType, altName, payload)
    local totalLen = string.len(payload)
    local totalChunks = math.ceil(totalLen / CHUNK_SIZE)
    if totalChunks == 0 then totalChunks = 1 end

    for i = 1, totalChunks do
        local startPos = ((i - 1) * CHUNK_SIZE) + 1
        local chunk = string.sub(payload, startPos, startPos + CHUNK_SIZE - 1)
        local msg = msgType .. "~" .. altName .. "~" .. i .. "~" .. totalChunks .. "~" .. chunk
        QueueMessage(msg)
    end
end

-- Checks pendingRelayChecks (populated by the SYNCREQ handler) and, for any
-- alt whose relay timer has come due, resends our cached copy of its data
-- -- unless the real bank alt (or someone else) has already answered for it
-- since the request came in, or we ourselves relayed it too recently.
ProcessPendingRelays = function()
    local now = time()
    local i = 1
    while i <= table.getn(pendingRelayChecks) do
        local check = pendingRelayChecks[i]
        if now >= check.fireAt then
            table.remove(pendingRelayChecks, i)

            local answeredAt = lastSyncActivityAt[check.altName] or 0
            local weRelayedAt = lastRelayedAt[check.altName] or 0
            local entry = GuildBankViewerDB.banks[check.altName]

            if entry and answeredAt < check.reqTime and (now - weRelayedAt) >= RELAY_SELF_COOLDOWN then
                lastRelayedAt[check.altName] = now
                lastSyncActivityAt[check.altName] = now
                local payload = BuildSyncPayload(entry.items, entry.gold, entry.lastUpdate)
                QueueChunks("RSYNC", check.altName, payload)
                Print("Relaying cached bank data for " .. check.altName .. " (bank alt appears offline).")
            end
        else
            i = i + 1
        end
    end
end

local function IsBankDataLoaded()
    -- The client doesn't have bank slot data until BankFrame has actually
    -- been shown once this session -- GetContainerNumSlots(-1) (and the
    -- bank bag slots) report 0 until then, even if the bank genuinely has
    -- items in it. Scanning at that point would silently produce a
    -- bags-only snapshot that looks like "the guild bank is nearly empty."
    return (GetContainerNumSlots(-1) or 0) > 0
end

BroadcastBankData = function(verbose, force)
    if not IsInGuild() then
        Print("You're not in a guild, so bank data can't be shared to a guild channel.")
        return
    end

    if not IsBankDataLoaded() then
        Print("Your bank hasn't been opened yet this session, so its contents aren't loaded -- skipping sync to avoid overwriting good data with an incomplete scan. Open your bank once (even just briefly), then try again.")
        return
    end

    local altName = UnitName("player")
    local items = ScanBagsAndBank()
    local gold = GetMoney()
    local now = time()
    local payload = BuildSyncPayload(items, gold, now)

    if verbose then
        local uniqueCount, totalCount = 0, 0
        for _, c in pairs(items) do
            uniqueCount = uniqueCount + 1
            totalCount = totalCount + c
        end
        Print("Scanned " .. uniqueCount .. " unique item stack(s), " .. totalCount .. " items total, for " .. altName .. ".")
    end

    if payload == lastBroadcastSignature and not force then
        return
    end
    lastBroadcastSignature = payload

    GuildBankViewerDB.banks[altName] = {
        items = items,
        gold = gold,
        lastUpdate = now,
        label = altName,
        isRelay = false,
        relayedBy = nil,
        guild = CurrentGuildKey(),
    }
    lastSyncActivityAt[altName] = now

    QueueChunks("SYNC", altName, payload)
end

-- Sent once per login by anyone whose local data might be stale/missing --
-- e.g. they weren't online the last time the bank alt or an officer
-- broadcast anything. The bank alt and current officers answer this by
-- resending their current data (see the SYNCREQ handler in OnAddonMessage).
local function RequestSync()
    if hasSentSyncRequest then return end
    if not IsInGuild() then return end
    hasSentSyncRequest = true
    QueueMessage("SYNCREQ~" .. UnitName("player"))
end

----------------------------------------------------------------------
-- Retiring a bank alt
--
-- Cached bank data otherwise lives forever -- nothing ever expired it, and
-- the relay feature actively keeps stale data alive by rebroadcasting it.
-- So unflagging a character as a bank alt (or an officer manually retiring
-- one that can no longer speak for itself) has to actively tell every
-- client, including relayers, to drop it -- not just stop updating it.
----------------------------------------------------------------------

local function PurgeBankAltLocally(altName)
    GuildBankViewerDB.banks[altName] = nil
    lastSyncActivityAt[altName] = nil
    lastRelayedAt[altName] = nil

    -- Also drop any relay we had queued up for this alt -- no point
    -- resending data we just threw away.
    local i = 1
    while i <= table.getn(pendingRelayChecks) do
        if pendingRelayChecks[i].altName == altName then
            table.remove(pendingRelayChecks, i)
        else
            i = i + 1
        end
    end

    if GuildBankViewerFrame and GuildBankViewerFrame:IsShown() then
        GuildBankViewer_RefreshList()
        GuildBankViewer_RefreshBankMoneyRows()
    end
end

-- altName retires itself (self) or an officer retires an alt on its
-- behalf (e.g. it's gone for good and can't come online to do it itself).
local function ForgetBankAlt(altName)
    PurgeBankAltLocally(altName)
    QueueMessage("FORGET~" .. altName)
end

----------------------------------------------------------------------
-- Item drag capture (used by the New Listing / New Bounty popups so you
-- can drag an item from your bags instead of typing its name)
----------------------------------------------------------------------

local pendingDragItem = nil -- { itemID = n, link = "..." }

local origPickupContainerItem = PickupContainerItem
PickupContainerItem = function(bag, slot)
    local link = GetContainerItemLink(bag, slot)
    if link then
        local id = GetItemIDFromLink(link)
        if id then
            pendingDragItem = { itemID = id, link = link }
        end
    end
    origPickupContainerItem(bag, slot)
end

----------------------------------------------------------------------
-- Selling board / Bounty board (shared logic)
----------------------------------------------------------------------

local function PostMarketEntry(kind, itemID, itemName, qty, amount)
    if not IsOfficer(UnitName("player")) then
        Print("Only guild officers can post to the " .. ((kind == "SELL") and "Selling" or "Bounty") .. " board.")
        return
    end

    qty = qty or 1
    amount = amount or 0
    itemName = SanitizeText(itemName)
    local me = UnitName("player")
    local id = me .. "-" .. time() .. "-" .. math.random(1000, 9999)

    local entry = { itemID = itemID, itemName = itemName, qty = qty, ts = time(), guild = CurrentGuildKey() }
    local store
    if kind == "SELL" then
        entry.price = amount
        entry.seller = me
        store = GuildBankViewerDB.listings
    else
        entry.reward = amount
        entry.poster = me
        store = GuildBankViewerDB.bounties
    end
    store[id] = entry

    QueueMessage(kind .. "~" .. id .. "~" .. itemID .. "~" .. qty .. "~" .. amount .. "~" .. itemName)

    if kind == "SELL" then
        Print("Listed " .. qty .. "x " .. itemName .. " for " .. FormatMoney(amount) .. ".")
        if GuildBankViewerFrame and GuildBankViewerFrame:IsShown() then GuildBankViewer_RefreshSelling() end
    else
        Print("Posted a bounty for " .. qty .. "x " .. itemName .. " (" .. FormatMoney(amount) .. ").")
        if GuildBankViewerFrame and GuildBankViewerFrame:IsShown() then GuildBankViewer_RefreshBounties() end
    end
end

local function CancelMarketEntry(kind, id)
    local store = (kind == "SELL") and GuildBankViewerDB.listings or GuildBankViewerDB.bounties
    local entry = store[id]
    if not entry then return end

    local owner = (kind == "SELL") and entry.seller or entry.poster
    if owner ~= UnitName("player") then return end -- can only remove your own

    store[id] = nil
    QueueMessage(kind .. "CANCEL~" .. id)

    if kind == "SELL" then
        if GuildBankViewerFrame and GuildBankViewerFrame:IsShown() then GuildBankViewer_RefreshSelling() end
    else
        if GuildBankViewerFrame and GuildBankViewerFrame:IsShown() then GuildBankViewer_RefreshBounties() end
    end
end

local function WhisperAbout(name, kindLabel, itemName, qty)
    if name == UnitName("player") then return end
    ChatFrame_OpenChat("/w " .. name .. " Hi, about your " .. kindLabel .. " for " .. qty .. "x " .. itemName .. " -- ", DEFAULT_CHAT_FRAME)
end

----------------------------------------------------------------------
-- Requests / tickets
----------------------------------------------------------------------

local function RequestItem(itemID, itemName, qty, altName)
    qty = qty or 1
    itemName = SanitizeText(itemName)
    local requester = UnitName("player")
    local ticketID = requester .. "-" .. time() .. "-" .. math.random(1000, 9999)

    GuildBankViewerDB.tickets[ticketID] = {
        itemID = itemID,
        itemName = itemName,
        qty = qty,
        altName = altName,
        requester = requester,
        status = "pending",
        ts = time(),
        guild = CurrentGuildKey(),
    }

    local msg = "REQ~" .. ticketID .. "~" .. itemID .. "~" .. qty .. "~" .. altName .. "~" .. requester .. "~" .. itemName
    QueueMessage(msg)
    Print("Requested " .. qty .. "x " .. itemName .. " from " .. altName .. ".")

    if GuildBankViewerTicketFrame and GuildBankViewerTicketFrame:IsShown() then
        GuildBankViewer_RefreshTickets()
    end
end

local function ActOnTicket(ticketID, newStatus)
    if not IsOfficer(UnitName("player")) then
        Print("Your guild rank isn't recognized as an officer, so this can't be sent.")
        return
    end

    local t = GuildBankViewerDB.tickets[ticketID]
    if not t then return end
    t.status = newStatus

    local msg = "REQACT~" .. ticketID .. "~" .. newStatus .. "~" .. UnitName("player")
    QueueMessage(msg)

    if newStatus == "approved" or newStatus == "denied" then
        if t.requester == UnitName("player") then
            -- You approved/denied your own request (e.g. testing solo) --
            -- the addon-message receive path never fires for messages you
            -- sent yourself, so notify directly here instead.
            Print("Your request for " .. t.qty .. "x " .. t.itemName .. " was " .. string.upper(newStatus) .. ".")
        else
            SendChatMessage(
                SanitizeText("Your guild bank request for " .. t.qty .. "x " .. t.itemName .. " was " .. newStatus .. "."),
                "WHISPER", nil, t.requester
            )
        end
    end

    if GuildBankViewerTicketFrame and GuildBankViewerTicketFrame:IsShown() then
        GuildBankViewer_RefreshTickets()
    end
end

----------------------------------------------------------------------
-- Receiving
----------------------------------------------------------------------

-- incoming[key] = { total = n, chunks = {[i]=chunk} }
-- Keyed by "<msgType>|<altName>" rather than just altName, so a live SYNC
-- for an alt and a relayed RSYNC for the same alt (which can legitimately
-- arrive interleaved -- e.g. the bank alt logs in mid-relay) don't corrupt
-- each other's partial chunks.
local incoming = {}

-- Shared by the SYNC and RSYNC branches below: reassemble chunks, and
-- return the completed payload string once every chunk has arrived (or nil
-- if the transmission isn't complete yet).
local function ReassembleChunk(key, idx, total, chunk)
    if idx == 1 or not incoming[key] or incoming[key].total ~= total then
        incoming[key] = { total = total, chunks = {} }
    end
    incoming[key].chunks[idx] = chunk

    for i = 1, total do
        if not incoming[key].chunks[i] then return nil end
    end

    local full = table.concat(incoming[key].chunks, "", 1, total)
    incoming[key] = nil
    return full
end

local function OnAddonMessage(prefix, message, channel, sender)
    if prefix ~= ADDON_PREFIX then return end
    if channel ~= "GUILD" then return end

    local _, _, msgType = string.find(message, "^(%a+)~")
    if not msgType then return end

    if msgType == "SYNC" then
        local _, _, altName, idxStr, totalStr, chunk = string.find(message, "^SYNC~([^~]+)~(%d+)~(%d+)~(.*)$")
        if not altName then return end

        -- A character can only report its OWN bank -- reject anyone claiming
        -- to sync data for a different alt name than the one actually sending.
        if altName ~= sender then return end

        local full = ReassembleChunk("SYNC|" .. altName, tonumber(idxStr), tonumber(totalStr), chunk)
        if full then
            local ts, gold, items = ParseSyncPayload(full)
            GuildBankViewerDB.banks[altName] = {
                items = items,
                gold = gold,
                lastUpdate = ts,
                label = altName,
                isRelay = false,
                relayedBy = nil,
                guild = CurrentGuildKey(),
            }
            -- Live data always beats anything relayed, and this tells our
            -- own relay-scheduling logic (see SYNCREQ below) that the real
            -- bank alt just answered, so nobody needs to relay for it now.
            lastSyncActivityAt[altName] = time()

            if GuildBankViewerFrame and GuildBankViewerFrame:IsShown() then
                GuildBankViewer_RefreshList()
            end
        end

    elseif msgType == "RSYNC" then
        -- Someone else is relaying cached bank data on behalf of an alt that
        -- isn't currently online to answer for itself. `sender` here is the
        -- relayer, NOT the bank alt -- that's expected and fine, unlike SYNC
        -- above there's no "altName must equal sender" check.
        local _, _, altName, idxStr, totalStr, chunk = string.find(message, "^RSYNC~([^~]+)~(%d+)~(%d+)~(.*)$")
        if not altName then return end

        local full = ReassembleChunk("RSYNC|" .. altName, tonumber(idxStr), tonumber(totalStr), chunk)
        if full then
            local ts, gold, items = ParseSyncPayload(full)

            -- Never let a relay clobber data we already have that's the
            -- same age or newer -- e.g. our own cache, or a live sync that
            -- came in while this relay was in flight.
            local existing = GuildBankViewerDB.banks[altName]
            if not existing or (existing.lastUpdate or 0) < ts then
                GuildBankViewerDB.banks[altName] = {
                    items = items,
                    gold = gold,
                    lastUpdate = ts,
                    label = altName,
                    isRelay = true,
                    relayedBy = sender,
                    guild = CurrentGuildKey(),
                }
                if GuildBankViewerFrame and GuildBankViewerFrame:IsShown() then
                    GuildBankViewer_RefreshList()
                end
            end

            -- Whether or not we kept it, someone has now answered for this
            -- alt on the channel -- don't let our own relay logic pile on.
            lastSyncActivityAt[altName] = time()
        end

    elseif msgType == "FORGET" then
        local _, _, altName = string.find(message, "^FORGET~(.+)$")
        if not altName then return end

        -- Only the alt itself (verified via the real addon-channel sender,
        -- same as SYNC above) or a current officer can retire an alt's
        -- data -- otherwise anyone could grief the guild's bank data by
        -- forging removals for alts that are still active.
        if sender == altName or IsOfficer(sender) then
            GuildBankViewerDB.banks[altName] = nil
            lastSyncActivityAt[altName] = nil
            lastRelayedAt[altName] = nil

            local i = 1
            while i <= table.getn(pendingRelayChecks) do
                if pendingRelayChecks[i].altName == altName then
                    table.remove(pendingRelayChecks, i)
                else
                    i = i + 1
                end
            end

            if GuildBankViewerFrame and GuildBankViewerFrame:IsShown() then
                GuildBankViewer_RefreshList()
                GuildBankViewer_RefreshBankMoneyRows()
            end
        end

    elseif msgType == "REQ" then
        local _, _, ticketID, itemID, qty, altName, itemName =
            string.find(message, "^REQ~([^~]+)~(%d+)~(%d+)~([^~]+)~[^~]+~(.*)$")
        if not ticketID then return end
        itemName = SanitizeText(itemName)

        -- Requester is always the real addon-channel sender, never a claim
        -- embedded in the message body.
        local requester = sender

        GuildBankViewerDB.tickets[ticketID] = {
            itemID = tonumber(itemID),
            itemName = itemName,
            qty = tonumber(qty),
            altName = altName,
            requester = requester,
            status = "pending",
            ts = time(),
            guild = CurrentGuildKey(),
        }

        if IsOfficer(UnitName("player")) then
            Print(requester .. " requested " .. qty .. "x " .. itemName .. " from " .. altName .. ".")
        end

        if GuildBankViewerTicketFrame and GuildBankViewerTicketFrame:IsShown() then
            GuildBankViewer_RefreshTickets()
        end

    elseif msgType == "REQACT" then
        local _, _, ticketID, newStatus = string.find(message, "^REQACT~([^~]+)~([^~]+)~")
        if not ticketID then return end

        -- Only honor this status change if the ACTUAL sender (per the game
        -- client, not any name written in the message) really holds an
        -- officer-level guild rank right now. A regular member's client
        -- could tick a box or edit the message all it wants -- every other
        -- client will still verify against the real roster and ignore it.
        if not IsOfficer(sender) then return end

        local t = GuildBankViewerDB.tickets[ticketID]
        if t then
            t.status = newStatus
            if t.requester == UnitName("player") then
                Print("Your request for " .. t.qty .. "x " .. t.itemName .. " was " .. string.upper(newStatus) .. " by " .. sender .. ".")
            end
        end

        if GuildBankViewerTicketFrame and GuildBankViewerTicketFrame:IsShown() then
            GuildBankViewer_RefreshTickets()
        end

    elseif msgType == "SYNCREQ" then
        -- Someone's local data might be stale or missing entirely (e.g. they
        -- weren't online the last time anything was broadcast). Only the
        -- bank alt and current officers have anything authoritative to
        -- resend, and each rate-limits itself so a handful of people
        -- logging in around the same time doesn't flood the channel.
        local now = time()

        if GuildBankViewerCharDB.isBankAlt and (now - lastSyncReqResponse) >= SYNC_REQ_COOLDOWN then
            lastSyncReqResponse = now
            BroadcastBankData(false, true)
        end

        -- Fallback relay: if we're not a bank alt ourselves but we have
        -- cached data for one, give the real bank alt(s) a few seconds to
        -- answer live first. If nothing shows up for a given alt by the
        -- time our check fires, we resend our cached copy of it so whoever
        -- asked isn't left with nothing just because a bank alt is offline.
        -- The jitter spreads different members' checks out in time so they
        -- don't all relay the same alt's data at once.
        local me = UnitName("player")
        local myGuild = CurrentGuildKey()
        for altName, data in pairs(GuildBankViewerDB.banks) do
            -- Only offer to relay data that's actually tagged for THIS
            -- guild -- our cache may also hold leftover data from a
            -- different guild (an old guild, an alt's guild, etc.) and
            -- that has no business being relayed onto this channel.
            if altName ~= me and myGuild and data.guild == myGuild then -- we already answered live for our own alt above, if applicable
                local jitter = math.random(0, RELAY_MAX_JITTER * 10) / 10
                table.insert(pendingRelayChecks, {
                    altName = altName,
                    fireAt = now + RELAY_MIN_DELAY + jitter,
                    reqTime = now,
                })
            end
        end

        if IsOfficer(UnitName("player")) and (now - lastMarketReqResponse) >= SYNC_REQ_COOLDOWN then
            lastMarketReqResponse = now
            local me = UnitName("player")
            for id, entry in pairs(GuildBankViewerDB.listings) do
                if entry.seller == me and myGuild and entry.guild == myGuild then
                    QueueMessage("SELL~" .. id .. "~" .. entry.itemID .. "~" .. entry.qty .. "~" .. entry.price .. "~" .. entry.itemName)
                end
            end
            for id, entry in pairs(GuildBankViewerDB.bounties) do
                if entry.poster == me and myGuild and entry.guild == myGuild then
                    QueueMessage("BOUNTY~" .. id .. "~" .. entry.itemID .. "~" .. entry.qty .. "~" .. entry.reward .. "~" .. entry.itemName)
                end
            end
        end
    end

    if msgType == "SELL" or msgType == "BOUNTY" then
        local _, _, id, itemID, qty, amount, itemName =
            string.find(message, "^" .. msgType .. "~([^~]+)~(%d+)~(%d+)~(%d+)~(.*)$")
        if not id then return end
        itemName = SanitizeText(itemName)

        -- These boards represent the GUILD BANK's own offers/requests --
        -- only accept them if the real sender currently holds officer rank.
        if not IsOfficer(sender) then return end

        local entry = { itemID = tonumber(itemID), itemName = itemName, qty = tonumber(qty), ts = time(), guild = CurrentGuildKey() }
        if msgType == "SELL" then
            entry.price = tonumber(amount)
            entry.seller = sender
            GuildBankViewerDB.listings[id] = entry
            if GuildBankViewerFrame and GuildBankViewerFrame:IsShown() then GuildBankViewer_RefreshSelling() end
        else
            entry.reward = tonumber(amount)
            entry.poster = sender
            GuildBankViewerDB.bounties[id] = entry
            if GuildBankViewerFrame and GuildBankViewerFrame:IsShown() then GuildBankViewer_RefreshBounties() end
        end

    elseif msgType == "SELLCANCEL" or msgType == "BOUNTYCANCEL" then
        local _, _, kind = string.find(msgType, "^(%a+)CANCEL$")
        local _, _, id = string.find(message, "^" .. msgType .. "~(.*)$")
        if not id then return end

        local store = (kind == "SELL") and GuildBankViewerDB.listings or GuildBankViewerDB.bounties
        local entry = store[id]
        if entry then
            local owner = (kind == "SELL") and entry.seller or entry.poster
            -- Only the real owner (verified by the actual message sender,
            -- not any embedded claim) can remove their own listing/bounty.
            if owner == sender then
                store[id] = nil
            end
        end

        if kind == "SELL" then
            if GuildBankViewerFrame and GuildBankViewerFrame:IsShown() then GuildBankViewer_RefreshSelling() end
        else
            if GuildBankViewerFrame and GuildBankViewerFrame:IsShown() then GuildBankViewer_RefreshBounties() end
        end
    end
end

----------------------------------------------------------------------
-- Event handling
----------------------------------------------------------------------

frame:RegisterEvent("ADDON_LOADED")
frame:RegisterEvent("PLAYER_LOGIN")
frame:RegisterEvent("PLAYER_GUILD_UPDATE")
frame:RegisterEvent("GUILD_ROSTER_UPDATE")
frame:RegisterEvent("CHAT_MSG_ADDON")
frame:RegisterEvent("BANKFRAME_OPENED")
frame:RegisterEvent("PLAYERBANKSLOTS_CHANGED")
frame:RegisterEvent("PLAYERBANKBAGSLOTS_CHANGED")
frame:RegisterEvent("ITEM_DATA_LOAD_RESULT") -- only ever fires if ClassicAPI (optional) is installed

frame:SetScript("OnEvent", function()
    if event == "ADDON_LOADED" and arg1 == "GuildBankViewer" then
        Print("Loaded. Click the minimap icon to open it (Settings/Tickets buttons are inside).")
    elseif event == "PLAYER_LOGIN" then
        RefreshGuildRoster()
        RequestSync()
    elseif event == "PLAYER_GUILD_UPDATE" then
        RefreshGuildRoster()
    elseif event == "GUILD_ROSTER_UPDATE" then
        RebuildRosterCache()
        if GuildBankViewerTicketFrame and GuildBankViewerTicketFrame:IsShown() then
            GuildBankViewer_RefreshTickets()
        end
        if GuildBankViewerSettingsFrame and GuildBankViewerSettingsFrame:IsShown() then
            GuildBankViewer_RefreshSettingsRankInfo()
        end
    elseif event == "CHAT_MSG_ADDON" then
        OnAddonMessage(arg1, arg2, arg3, arg4)
    elseif event == "BANKFRAME_OPENED"
        or event == "PLAYERBANKSLOTS_CHANGED" or event == "PLAYERBANKBAGSLOTS_CHANGED" then
        -- BANKFRAME_CLOSED deliberately isn't handled here (and isn't even
        -- registered above). It used to be, but that scheduled a scan for
        -- ~0.75s after the bank window closed -- by which point the client
        -- no longer has real bank slot contents to read, so that scan came
        -- back looking like an almost-empty bank (bags only) and overwrote
        -- the good data that was just synced while the bank was open. Only
        -- scan while the bank is actually open (or about to be, for the
        -- OPENED case) so a close never has anything to clobber good data
        -- with.
        if GuildBankViewerCharDB.isBankAlt then
            -- Don't scan instantly: right when BANKFRAME_OPENED fires, the
            -- bank's slot contents can still be a beat behind arriving from
            -- the server (bag contents don't have this problem -- they're
            -- already loaded from login), so scanning immediately can catch
            -- an empty bank and broadcast bag items only, with the bank
            -- itself looking empty to everyone else. A short delay lets the
            -- data actually land, and also coalesces several rapid
            -- slot-changed events (e.g. moving a whole stack around) into
            -- one scan instead of one per event.
            pendingBankScanAt = GetTime() + 0.75
        end
    elseif event == "ITEM_DATA_LOAD_RESULT" then
        -- ClassicAPI (optional) tells us an item we didn't have cached just
        -- loaded. This is also what resolves a missing icon (icon texture
        -- comes from the same item data as the name) -- but only the Bank
        -- tab was being refreshed here, so a Selling/Bounty row with an
        -- unresolved icon at listing time would stay stuck on the
        -- placeholder until something else happened to trigger a redraw
        -- (switching tabs, searching, etc.). Refresh whichever of the
        -- three lists are actually showing.
        if GuildBankViewerFrame and GuildBankViewerFrame:IsShown() then
            GuildBankViewer_RefreshList()
            GuildBankViewer_RefreshSelling()
            GuildBankViewer_RefreshBounties()
        end
    end
end)

----------------------------------------------------------------------
-- UI: main browse/search window
----------------------------------------------------------------------

local ROW_HEIGHT = 18
local ITEM_ROW_HEIGHT = 30 -- taller than ROW_HEIGHT: used for Bank/Selling/Bounty
                            -- rows specifically, which now carry a bigger icon and
                            -- a name column that can wrap to a second line without
                            -- overlapping the row below (tickets don't need this)
local ITEM_ROW_GAP = 3     -- a little breathing room between item rows
local ITEM_ICON_SIZE = 20
local MAX_NUM_ROWS = 22 -- pool size; how many rows actually show is dynamic, see UpdateBankListSize
local NUM_ROWS = 17     -- current visible row count, adjusted per how much space the alt gold tracker needs
local rows = {}

-- Faint zebra-striping for list rows: odd slots stay transparent (the
-- list's own background shows through), even slots get a subtle white
-- wash. Kept low-alpha so it reads as a stripe, not a highlight.
local function SetRowStripe(row, slotIndex)
    if math.mod(slotIndex, 2) == 0 then
        row.bg:SetTexture(1, 1, 1, 0.045)
    else
        row.bg:SetTexture(1, 1, 1, 0)
    end
end

-- Height a list box needs to fully contain n rows: 8px padding above the
-- first row, 8px below the last, ITEM_ROW_HEIGHT per row, and ITEM_ROW_GAP
-- between each pair of rows (n-1 gaps, not n -- there's no gap trailing
-- the last row). Leaving the gaps out of this sum (as an earlier version
-- did) undercounts the box by a few px per row and lets the last row spill
-- past the bottom border -- invisible when rows had no background of their
-- own, but obvious now that each row draws a stripe.
local function ListContentHeight(n)
    if n <= 0 then return 16 end
    return 16 + n * ITEM_ROW_HEIGHT + (n - 1) * ITEM_ROW_GAP
end

-- Same span, minus the 16px of box padding -- this is the actual pixel
-- distance from the top of the first row to the bottom of the last row,
-- which is what the scroll frame's height should match. The scrollbar
-- Blizzard's FauxScrollFrameTemplate draws is stretched to fit the scroll
-- frame's own height, so if this comes up short (as a plain n *
-- ITEM_ROW_HEIGHT does once gaps are added between rows), the bar's track
-- visibly stops short of the list's actual bottom row.
local function RowsSpanHeight(n)
    if n <= 0 then return 0 end
    return n * ITEM_ROW_HEIGHT + (n - 1) * ITEM_ROW_GAP
end
local sortedResults = {}

local function TryRequestUnknownItem(itemID)
    -- Optional: if ClassicAPI's DLL is installed, this asks the server for item
    -- data we don't have cached yet, so the name resolves instead of staying
    -- "Item #12345". No-ops silently if ClassicAPI isn't present.
    if C_Item and C_Item.RequestLoadItemData then
        pcall(C_Item.RequestLoadItemData, itemID)
    end
end

-- Column sorting, shared across the Bank/Selling/Bounty lists. Each list
-- gets its own entry here: column, ascending direction, and the header
-- widgets (populated by MakeSortHeader when each tab's UI is built).
local sortState = {
    bank = { column = "name", ascending = true, headers = {} },
    sell = { column = "ts", ascending = false, headers = {} },
    bounty = { column = "ts", ascending = false, headers = {} },
}

local function GuildBankViewer_UpdateSortHeaders(listKey)
    local state = sortState[listKey]
    for column, h in pairs(state.headers) do
        h.label:SetText(h.baseLabel)
        if column == state.column then
            h.arrow:Show()
            if state.ascending then
                h.arrow:SetTexCoord(0, 1, 0, 1)
            else
                h.arrow:SetTexCoord(0, 1, 1, 0) -- vertical flip for descending
            end
        else
            h.arrow:Hide()
        end
    end
end

function GuildBankViewer_SortBy(listKey, column)
    local state = sortState[listKey]
    if state.column == column then
        state.ascending = not state.ascending
    else
        state.column = column
        state.ascending = true
    end
    GuildBankViewer_UpdateSortHeaders(listKey)
    if listKey == "bank" then
        GuildBankViewer_RefreshList()
    elseif listKey == "sell" then
        GuildBankViewer_RefreshSelling()
    else
        GuildBankViewer_RefreshBounties()
    end
end

-- Creates a clickable column header with a show/hide sort-direction arrow.
-- listKey picks which list it drives ("bank"/"sell"/"bounty"); column is
-- the sort key it activates; rarityOnRightClick, if set, makes right-click
-- sort by item rarity instead (used on the Item column of each tab).
local function MakeSortHeader(listKey, page, column, text, x, y, width, tooltip, rarityOnRightClick)
    local btn = CreateFrame("Button", nil, page)
    btn:SetPoint("TOPLEFT", page, "TOPLEFT", x, y)
    btn:SetWidth(width)
    btn:SetHeight(14)

    local label = btn:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    label:SetPoint("LEFT", btn, "LEFT", 0, 0)
    label:SetJustifyH("LEFT")
    label:SetText(text)

    local arrow = btn:CreateTexture(nil, "OVERLAY")
    arrow:SetTexture("Interface\\Buttons\\UI-SortArrow")
    arrow:SetWidth(10)
    arrow:SetHeight(10)
    arrow:SetPoint("LEFT", label, "RIGHT", 3, 0)
    arrow:Hide()

    btn:RegisterForClicks("LeftButtonUp", "RightButtonUp")
    btn:SetScript("OnClick", function()
        if rarityOnRightClick and arg1 == "RightButton" then
            GuildBankViewer_SortBy(listKey, "quality")
        else
            GuildBankViewer_SortBy(listKey, column)
        end
    end)
    btn:SetScript("OnEnter", function()
        label:SetTextColor(1, 1, 1)
        if tooltip then
            GameTooltip:SetOwner(btn, "ANCHOR_TOP")
            GameTooltip:SetText(tooltip, nil, nil, nil, nil, true)
            GameTooltip:Show()
        end
    end)
    btn:SetScript("OnLeave", function()
        label:SetTextColor(1, 0.82, 0)
        GameTooltip:Hide()
    end)
    sortState[listKey].headers[column] = { label = label, arrow = arrow, baseLabel = text }
end

local function BuildResults(filterText)
    sortedResults = {}
    filterText = filterText and string.lower(filterText) or ""
    local state = sortState.bank
    local myGuild = CurrentGuildKey()

    for altName, data in pairs(GuildBankViewerDB.banks) do
      if myGuild and data.guild == myGuild then
        for key, count in pairs(data.items) do
            local _, _, idStr, suffixStr = string.find(key, "(%-?%d+):(%-?%d+)")
            local itemID = tonumber(idStr)
            local suffixID = tonumber(suffixStr) or 0
            if itemID then
                -- Only bother building a synthetic suffixed link when there
                -- actually is a suffix -- for the common case (suffixID 0)
                -- the bare itemID behaves exactly as it always did.
                local lookup = (suffixID ~= 0) and BuildItemLink(itemID, suffixID) or itemID
                local name, link, quality = GetItemInfo(lookup)
                -- Icon art never changes with a random suffix (Green Lens of
                -- Fire Resistance uses the exact same icon as plain Green
                -- Lens) -- always resolve it from the bare itemID rather
                -- than the synthetic link. The synthetic link reliably
                -- resolves a name on this server but not always a texture,
                -- which was showing the "?" placeholder for every suffixed
                -- item even though the name/count were already correct.
                local texture = SafeGetItemIcon(itemID)
                if not name then
                    TryRequestUnknownItem(itemID)
                    name = "Item #" .. itemID
                end
                if filterText == "" or string.find(string.lower(name), filterText, 1, true) then
                    table.insert(sortedResults, {
                        itemID = itemID,
                        suffixID = suffixID,
                        name = name,
                        link = link,
                        quality = quality or 1,
                        texture = texture,
                        count = count,
                        altName = altName,
                        isRelay = data.isRelay,
                        relayedBy = data.relayedBy,
                        lastUpdate = data.lastUpdate,
                    })
                end
            end
        end
      end
    end

    table.sort(sortedResults, function(a, b)
        local av, bv
        if state.column == "count" then
            av, bv = a.count, b.count
        elseif state.column == "alt" then
            av, bv = a.altName, b.altName
        elseif state.column == "quality" then
            av, bv = a.quality, b.quality
        else
            av, bv = a.name, b.name
        end

        if av == bv then
            -- Stable tie-break so equal-sort-key rows don't jump around.
            if a.name ~= b.name then return a.name < b.name end
            return a.altName < b.altName
        end

        if state.ascending then
            return av < bv
        else
            return av > bv
        end
    end)
end

-- Thin global wrapper around the money-row refresher that lives inside
-- CreateMainFrame (as GuildBankViewerFrame.RefreshBankAltRows). Being a
-- global, this can be called immediately -- e.g. from ForgetBankAlt or the
-- FORGET handler above, both of which run before CreateMainFrame is ever
-- called -- since Lua only needs the global to exist by the time it's
-- actually invoked, not by the time it's textually referenced.
function GuildBankViewer_RefreshBankMoneyRows()
    if GuildBankViewerFrame and GuildBankViewerFrame.RefreshBankAltRows then
        GuildBankViewerFrame.RefreshBankAltRows()
    end
end

function GuildBankViewer_RefreshList()
    local searchBox = getglobal("GuildBankViewerSearchBox")
    local filterText = searchBox and searchBox:GetText() or ""
    BuildResults(filterText)

    local offset = FauxScrollFrame_GetOffset(GuildBankViewerScrollFrame) or 0
    FauxScrollFrame_Update(GuildBankViewerScrollFrame, table.getn(sortedResults), NUM_ROWS, ITEM_ROW_HEIGHT)

    for i = 1, MAX_NUM_ROWS do
        local row = rows[i]
        local dataIndex = i + offset
        local entry = (i <= NUM_ROWS) and sortedResults[dataIndex] or nil
        if entry then
            local r, g, b = 1, 1, 1
            if entry.quality and ITEM_QUALITY_COLORS and ITEM_QUALITY_COLORS[entry.quality] then
                local c = ITEM_QUALITY_COLORS[entry.quality]
                r, g, b = c.r, c.g, c.b
            end
            row.name:SetText(entry.name)
            row.name:SetTextColor(r, g, b)
            row.count:SetText(tostring(entry.count))
            if entry.isRelay then
                -- Data for this alt came from another member's cache, not
                -- live from the alt itself -- flag it so people know it
                -- might be a bit older than usual.
                row.alt:SetText(entry.altName .. " |cffffcc00(cached)|r")
            else
                row.alt:SetText(entry.altName)
            end
            row.icon:SetTexture(SafeIconTexture(entry.texture))
            row.link = entry.link
            row.itemID = entry.itemID
            row.suffixID = entry.suffixID
            row.itemName = entry.name
            row.altName = entry.altName
            row.maxCount = entry.count
            row.isRelay = entry.isRelay
            row.relayedBy = entry.relayedBy
            row.lastUpdate = entry.lastUpdate
            SetRowStripe(row, i)
            row:Show()
            row.reqBtn:Show()
        else
            row:Hide()
            row.reqBtn:Hide()
        end
    end
end

local function CreateRow(parent, index)
    local row = CreateFrame("Button", "GuildBankViewerRow" .. index, parent)
    row:SetHeight(ITEM_ROW_HEIGHT)
    row:SetWidth(460) -- narrowed from 468 (previously over-narrowed to 396,
                       -- then under-tightened to 454) so the row's own
                       -- background and the Request button end just clear
                       -- of the scrollbar with a small, deliberate margin
    if index == 1 then
        row:SetPoint("TOPLEFT", parent, "TOPLEFT", 8, -8)
    else
        row:SetPoint("TOPLEFT", rows[index - 1], "BOTTOMLEFT", 0, -ITEM_ROW_GAP)
    end

    -- Zebra-striped background so adjacent rows are easy to tell apart at
    -- a glance. Stretched a couple pixels past the row's own bounds so it
    -- also fills the small ITEM_ROW_GAP between rows instead of leaving
    -- visible seams of the list's own background showing through.
    row.bg = row:CreateTexture(nil, "BACKGROUND")
    row.bg:SetPoint("TOPLEFT", row, "TOPLEFT", -4, math.floor(ITEM_ROW_GAP / 2) + 1)
    row.bg:SetPoint("BOTTOMRIGHT", row, "BOTTOMRIGHT", 4, -(math.floor(ITEM_ROW_GAP / 2) + 1))
    row.bg:SetTexture(1, 1, 1, 1)

    row.icon = row:CreateTexture(nil, "ARTWORK")
    row.icon:SetWidth(ITEM_ICON_SIZE)
    row.icon:SetHeight(ITEM_ICON_SIZE)
    row.icon:SetPoint("TOPLEFT", row, "TOPLEFT", 0, -5)

    -- Columns end 52px earlier than before (name is narrower; count/alt/
    -- Request all shift left by the same 52px, so the gaps between them
    -- stay identical) to keep the Request button clear of the scrollbar.
    -- FauxScrollFrameTemplate's scrollbar is inset -13 from the *scroll
    -- frame's* own right edge (which is narrower than the row/listBg), not
    -- from the row's right edge, so it sat under the button before this.
    row.name = row:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    row.name:SetPoint("TOPLEFT", row, "TOPLEFT", 26, -6)
    row.name:SetWidth(216)
    row.name:SetJustifyH("LEFT")
    row.name:SetJustifyV("TOP")

    row.count = row:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    row.count:SetPoint("TOPLEFT", row, "TOPLEFT", 248, -6)
    row.count:SetWidth(40)

    row.alt = row:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    row.alt:SetPoint("TOPLEFT", row, "TOPLEFT", 294, -6)
    row.alt:SetWidth(90)
    row.alt:SetJustifyH("LEFT")

    local reqBtn = CreateFrame("Button", "GuildBankViewerRow" .. index .. "Req", row, "UIPanelButtonTemplate")
    reqBtn:SetWidth(60)
    reqBtn:SetHeight(18)
    reqBtn:SetPoint("TOPLEFT", row, "TOPLEFT", 396, -4)
    reqBtn:SetText("Request")
    local reqBtnText = getglobal(reqBtn:GetName() .. "Text")
    reqBtnText:SetFontObject("GameFontNormalSmall")
    reqBtnText:SetFont("Fonts\\FRIZQT__.ttf", 10)
    reqBtn:SetScript("OnClick", function()
        GuildBankViewer_PendingItemID = row.itemID
        GuildBankViewer_PendingItemName = row.itemName
        GuildBankViewer_PendingAltName = row.altName
        StaticPopup_Show("GUILDBANKVIEWER_REQUEST", row.itemName)
    end)
    row.reqBtn = reqBtn

    row:SetScript("OnEnter", function()
        if this.link then
            GameTooltip:SetOwner(this, "ANCHOR_CURSOR")
            GameTooltip:SetHyperlink(this.link)
            if this.isRelay then
                local ageMin = math.floor((time() - (this.lastUpdate or time())) / 60)
                GameTooltip:AddLine(" ", 1, 1, 1)
                GameTooltip:AddLine(this.altName .. " was offline; showing data relayed by " .. (this.relayedBy or "?") .. ".", 1, 0.82, 0)
                GameTooltip:AddLine("As of about " .. ageMin .. " minute(s) ago.", 0.7, 0.7, 0.7)
            end
            GameTooltip:Show()
        end
    end)
    row:SetScript("OnLeave", function()
        GameTooltip:Hide()
    end)

    return row
end

----------------------------------------------------------------------
-- Selling / Bounty board rows (shared row layout, used by both tabs)
----------------------------------------------------------------------

local MARKET_NUM_ROWS = 22 -- pool size
-- How many rows actually fit in the fixed space the Selling/Bounty pages
-- give the list (same layout math as UpdateBankListSize, but these two
-- pages don't have a variable-height footer to account for). The box is
-- always sized to this, same as the Bank tab's list -- it fills the full
-- available height regardless of how many listings currently exist.
local MARKET_MAX_VISIBLE_ROWS = 8
for n = 8, MARKET_NUM_ROWS do
    if ListContentHeight(n) <= (596 - 141 - 10 - 16 - 30) then
        MARKET_MAX_VISIBLE_ROWS = n
    else
        break
    end
end
local sellingRows = {}
local bountyRows = {}
local sortedSelling = {}
local sortedBounties = {}

----------------------------------------------------------------------
-- Pending item info poller
--
-- On a vanilla client, GetItemInfo()/GetItemIcon() return nil the first
-- time they're asked about an item this client has never cached before
-- (e.g. a guild bank item nobody local has looked at yet). That first
-- call silently queues a server query, but nothing tells us when the
-- answer comes back -- retail's GET_ITEM_INFO_RECEIVED event doesn't
-- exist here, unless the optional ClassicAPI addon is installed (see
-- TryRequestUnknownItem/ITEM_DATA_LOAD_RESULT above). Without it, a row
-- is stuck on "Item #12345" and a question-mark icon until something
-- else happens to rebuild the list -- switching tabs and back "fixes"
-- it only because the query has usually resolved by then. This just
-- retries the rebuild itself every fraction of a second while the
-- visible tab still has something unresolved, so it self-corrects
-- without needing a manual nudge.
----------------------------------------------------------------------

local PENDING_INFO_INTERVAL = 0.3
local PENDING_INFO_MAX_WAIT = 10 -- give up (per tab-view) after this long, so
                                  -- an item that will just never resolve (e.g.
                                  -- removed from the server's item table)
                                  -- can't spin this forever
local pendingInfoElapsed = 0
local pendingInfoWaited = 0
local pendingInfoLastTab = nil

local function AnyMissingTexture(list)
    for _, entry in pairs(list) do
        if not entry.texture then
            return true
        end
    end
    return false
end

local pendingInfoPoller = CreateFrame("Frame")
pendingInfoPoller:SetScript("OnUpdate", function()
    if not (GuildBankViewerFrame and GuildBankViewerFrame:IsShown()) then
        pendingInfoWaited = 0
        pendingInfoLastTab = nil
        return
    end

    pendingInfoElapsed = pendingInfoElapsed + arg1
    if pendingInfoElapsed < PENDING_INFO_INTERVAL then return end
    pendingInfoElapsed = 0

    local tab = GuildBankViewerFrame.activeTab
    if tab ~= pendingInfoLastTab then
        pendingInfoLastTab = tab
        pendingInfoWaited = 0
    end

    local list = sortedResults
    if tab == "sell" then
        list = sortedSelling
    elseif tab == "bounty" then
        list = sortedBounties
    end

    if not AnyMissingTexture(list) then
        pendingInfoWaited = 0
        return
    end

    if pendingInfoWaited > PENDING_INFO_MAX_WAIT then
        return
    end
    pendingInfoWaited = pendingInfoWaited + PENDING_INFO_INTERVAL

    if tab == "sell" then
        GuildBankViewer_RefreshSelling()
    elseif tab == "bounty" then
        GuildBankViewer_RefreshBounties()
    else
        GuildBankViewer_RefreshList()
    end
end)

local function BuildMarket(listKey, store, filterText)
    local result = {}
    filterText = filterText and string.lower(filterText) or ""
    local myGuild = CurrentGuildKey()
    for id, entry in pairs(store) do
      if myGuild and entry.guild == myGuild then
        local name, link, quality = GetItemInfo(entry.itemID)
        local texture = SafeGetItemIcon(entry.itemID)
        if not name then
            TryRequestUnknownItem(entry.itemID)
            name = entry.itemName or ("Item #" .. entry.itemID)
        end
        if filterText == "" or string.find(string.lower(name), filterText, 1, true) then
            table.insert(result, {
                id = id,
                itemID = entry.itemID,
                name = name,
                link = link,
                quality = quality or 1,
                texture = texture,
                qty = entry.qty,
                amount = entry.price or entry.reward,
                poster = entry.seller or entry.poster,
                ts = entry.ts,
            })
        end
      end
    end

    local state = sortState[listKey]
    table.sort(result, function(a, b)
        local av, bv
        if state.column == "qty" then
            av, bv = a.qty, b.qty
        elseif state.column == "amount" then
            av, bv = a.amount, b.amount
        elseif state.column == "poster" then
            av, bv = a.poster, b.poster
        elseif state.column == "quality" then
            av, bv = a.quality, b.quality
        elseif state.column == "name" then
            av, bv = a.name, b.name
        else -- "ts": most recently posted
            av, bv = a.ts, b.ts
        end

        if av == bv then
            if a.name ~= b.name then return a.name < b.name end
            return (a.ts or 0) > (b.ts or 0)
        end

        if state.ascending then
            return av < bv
        else
            return av > bv
        end
    end)
    return result
end

local function RefreshMarketRows(rowPool, sortedData, scrollFrameName, kind)
    local scrollFrame = getglobal(scrollFrameName)
    local offset = FauxScrollFrame_GetOffset(scrollFrame) or 0
    FauxScrollFrame_Update(scrollFrame, table.getn(sortedData), MARKET_MAX_VISIBLE_ROWS, ITEM_ROW_HEIGHT)

    for i = 1, MARKET_NUM_ROWS do
        local row = rowPool[i]
        local dataIndex = i + offset
        local entry = (i <= MARKET_MAX_VISIBLE_ROWS) and sortedData[dataIndex] or nil
        if entry then
            local r, g, b = 1, 1, 1
            if entry.quality and ITEM_QUALITY_COLORS and ITEM_QUALITY_COLORS[entry.quality] then
                local c = ITEM_QUALITY_COLORS[entry.quality]
                r, g, b = c.r, c.g, c.b
            end
            row.name:SetText(entry.name)
            row.name:SetTextColor(r, g, b)
            row.qty:SetText(tostring(entry.qty))
            row.amount:SetText(FormatMoney(entry.amount))
            row.poster:SetText(entry.poster)
            row.icon:SetTexture(SafeIconTexture(entry.texture))
            row.link = entry.link
            row.entryID = entry.id
            row.itemName = entry.name
            row.qtyVal = entry.qty
            row.posterName = entry.poster

            local actionBtnText = getglobal(row.actionBtn:GetName() .. "Text")
            if entry.poster == UnitName("player") then
                row.actionBtn:SetText("Remove")
                row.actionBtn:SetScript("OnClick", function()
                    CancelMarketEntry(kind, row.entryID)
                end)
            else
                row.actionBtn:SetText("Whisper")
                row.actionBtn:SetScript("OnClick", function()
                    local kindLabel = (kind == "SELL") and "listing" or "bounty"
                    WhisperAbout(row.posterName, kindLabel, row.itemName, row.qtyVal)
                end)
            end
            actionBtnText:SetFontObject("GameFontNormalSmall")
            actionBtnText:SetFont("Fonts\\FRIZQT__.ttf", 10)
            SetRowStripe(row, i)
            row:Show()
        else
            row:Hide()
        end
    end
end

function GuildBankViewer_RefreshSelling()
    local searchBox = getglobal("GuildBankViewerSellSearchBox")
    local filterText = searchBox and searchBox:GetText() or ""
    sortedSelling = BuildMarket("sell", GuildBankViewerDB.listings, filterText)
    RefreshMarketRows(sellingRows, sortedSelling, "GuildBankViewerSellScrollFrame", "SELL")
end

function GuildBankViewer_RefreshBounties()
    local searchBox = getglobal("GuildBankViewerBountySearchBox")
    local filterText = searchBox and searchBox:GetText() or ""
    sortedBounties = BuildMarket("bounty", GuildBankViewerDB.bounties, filterText)
    RefreshMarketRows(bountyRows, sortedBounties, "GuildBankViewerBountyScrollFrame", "BOUNTY")
end

local function CreateMarketRow(parent, index, rowPool, namePrefix)
    local row = CreateFrame("Button", "GuildBankViewer" .. namePrefix .. "Row" .. index, parent)
    row:SetHeight(ITEM_ROW_HEIGHT)
    row:SetWidth(461) -- narrowed from 484 (previously over-narrowed to 396,
                       -- then under-tightened to 455) so the row's own
                       -- background and the action button end just clear
                       -- of the scrollbar with a small, deliberate margin
    if index == 1 then
        row:SetPoint("TOPLEFT", parent, "TOPLEFT", 8, -8)
    else
        row:SetPoint("TOPLEFT", rowPool[index - 1], "BOTTOMLEFT", 0, -ITEM_ROW_GAP)
    end

    row.bg = row:CreateTexture(nil, "BACKGROUND")
    row.bg:SetPoint("TOPLEFT", row, "TOPLEFT", -4, math.floor(ITEM_ROW_GAP / 2) + 1)
    row.bg:SetPoint("BOTTOMRIGHT", row, "BOTTOMRIGHT", 4, -(math.floor(ITEM_ROW_GAP / 2) + 1))
    row.bg:SetTexture(1, 1, 1, 1)

    row.icon = row:CreateTexture(nil, "ARTWORK")
    row.icon:SetWidth(ITEM_ICON_SIZE)
    row.icon:SetHeight(ITEM_ICON_SIZE)
    row.icon:SetPoint("TOPLEFT", row, "TOPLEFT", 0, -5)

    -- Same 67px leftward compression as the Bank tab's row (see CreateRow)
    -- and for the same reason: the scrollbar sits inset within the scroll
    -- frame's own (narrower) width, not the row's, so the action button was
    -- sitting right under it. Name is narrower; everything after it shifts
    -- left by the same amount so the gaps between columns don't change.
    row.name = row:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    row.name:SetPoint("TOPLEFT", row, "TOPLEFT", 26, -6)
    row.name:SetWidth(148)
    row.name:SetJustifyH("LEFT")
    row.name:SetJustifyV("TOP")

    row.qty = row:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    row.qty:SetPoint("TOPLEFT", row, "TOPLEFT", 180, -6)
    row.qty:SetWidth(30)

    row.amount = row:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    row.amount:SetPoint("TOPLEFT", row, "TOPLEFT", 216, -6)
    row.amount:SetWidth(70)
    row.amount:SetJustifyH("LEFT")

    row.poster = row:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    row.poster:SetPoint("TOPLEFT", row, "TOPLEFT", 292, -6)
    row.poster:SetWidth(90)
    row.poster:SetJustifyH("LEFT")

    local actionBtn = CreateFrame("Button", "GuildBankViewer" .. namePrefix .. "Row" .. index .. "Act", row, "UIPanelButtonTemplate")
    actionBtn:SetWidth(64)
    actionBtn:SetHeight(18)
    actionBtn:SetPoint("TOPLEFT", row, "TOPLEFT", 392, -4)
    local actionBtnText = getglobal(actionBtn:GetName() .. "Text")
    actionBtnText:SetFontObject("GameFontNormalSmall")
    actionBtnText:SetFont("Fonts\\FRIZQT__.ttf", 10)
    row.actionBtn = actionBtn

    row:SetScript("OnEnter", function()
        if this.link then
            GameTooltip:SetOwner(this, "ANCHOR_CURSOR")
            GameTooltip:SetHyperlink(this.link)
            GameTooltip:Show()
        end
    end)
    row:SetScript("OnLeave", function()
        GameTooltip:Hide()
    end)

    return row
end

local MAX_ALT_MONEY_ROWS = 4

local function CreateMainFrame()
    local f = CreateFrame("Frame", "GuildBankViewerFrame", UIParent)
    f:SetWidth(530)
    f:SetHeight(596)
    f:SetPoint("CENTER", UIParent, "CENTER", 0, 0)
    f:SetFrameStrata("HIGH")
    f:SetBackdrop({
        bgFile = "Interface\\DialogFrame\\UI-DialogBox-Background",
        edgeFile = "Interface\\DialogFrame\\UI-DialogBox-Border",
        tile = true, tileSize = 32, edgeSize = 32,
        insets = { left = 11, right = 12, top = 12, bottom = 11 },
    })
    f:SetMovable(true)
    f:EnableMouse(true)
    f:RegisterForDrag("LeftButton")
    f:SetScript("OnDragStart", function() this:StartMoving() end)
    f:SetScript("OnDragStop", function() this:StopMovingOrSizing() end)
    f:Hide()

    local title = f:CreateFontString(nil, "OVERLAY", "GameFontNormalLarge")
    title:SetPoint("TOP", f, "TOP", 0, -16)
    title:SetText("Guild Bank Viewer")

    local closeBtn = CreateFrame("Button", nil, f, "UIPanelCloseButton")
    closeBtn:SetPoint("TOPRIGHT", f, "TOPRIGHT", -5, -5)

    -- Settings/Tickets sit on their own row, well clear of the close button.
    local ticketsBtn = CreateFrame("Button", "GuildBankViewerOpenTicketsBtn", f, "UIPanelButtonTemplate")
    ticketsBtn:SetWidth(80)
    ticketsBtn:SetHeight(20)
    ticketsBtn:SetPoint("TOPRIGHT", f, "TOPRIGHT", -20, -40)
    ticketsBtn:SetText("Tickets")
    ticketsBtn:SetScript("OnClick", function()
        GuildBankViewer_OpenTickets()
    end)

    local settingsBtn = CreateFrame("Button", "GuildBankViewerOpenSettingsBtn", f, "UIPanelButtonTemplate")
    settingsBtn:SetWidth(80)
    settingsBtn:SetHeight(20)
    settingsBtn:SetPoint("RIGHT", ticketsBtn, "LEFT", -6, 0)
    settingsBtn:SetText("Settings")
    settingsBtn:SetScript("OnClick", function()
        GuildBankViewer_OpenSettings()
    end)

    ------------------------------------------------------------------
    -- Tab strip
    ------------------------------------------------------------------

    local tabBank = CreateFrame("Button", "GuildBankViewerTabBank", f, "UIPanelButtonTemplate")
    tabBank:SetWidth(90)
    tabBank:SetHeight(22)
    tabBank:SetPoint("TOPLEFT", f, "TOPLEFT", 20, -66)
    tabBank:SetText("Bank")

    local tabSell = CreateFrame("Button", "GuildBankViewerTabSell", f, "UIPanelButtonTemplate")
    tabSell:SetWidth(90)
    tabSell:SetHeight(22)
    tabSell:SetPoint("LEFT", tabBank, "RIGHT", 4, 0)
    tabSell:SetText("Selling")

    local tabBounty = CreateFrame("Button", "GuildBankViewerTabBounty", f, "UIPanelButtonTemplate")
    tabBounty:SetWidth(90)
    tabBounty:SetHeight(22)
    tabBounty:SetPoint("LEFT", tabSell, "RIGHT", 4, 0)
    tabBounty:SetText("Bounties")

    ------------------------------------------------------------------
    -- Page: Bank
    ------------------------------------------------------------------

    local bankPage = CreateFrame("Frame", nil, f)
    bankPage:SetAllPoints(f)

    local searchLabel = bankPage:CreateFontString(nil, "OVERLAY", "GameFontNormal")
    searchLabel:SetPoint("TOPLEFT", bankPage, "TOPLEFT", 20, -98)
    searchLabel:SetText("Search:")

    local searchBox = CreateFrame("EditBox", "GuildBankViewerSearchBox", bankPage, "InputBoxTemplate")
    searchBox:SetWidth(200)
    searchBox:SetHeight(20)
    searchBox:SetPoint("LEFT", searchLabel, "RIGHT", 10, 0)
    searchBox:SetAutoFocus(false)
    searchBox:SetScript("OnTextChanged", function() GuildBankViewer_RefreshList() end)
    searchBox:SetScript("OnEscapePressed", function() this:ClearFocus() end)

    MakeSortHeader("bank", bankPage, "name", "Item", 50, -125, 216, "Click to sort alphabetically.\nRight-click to sort by rarity.", true)
    MakeSortHeader("bank", bankPage, "count", "Count", 272, -125, 40)
    MakeSortHeader("bank", bankPage, "alt", "Bank Alt", 318, -125, 90)
    GuildBankViewer_UpdateSortHeaders("bank")

    local listBg = CreateFrame("Frame", nil, bankPage)
    listBg:SetPoint("TOPLEFT", bankPage, "TOPLEFT", 16, -141)
    listBg:SetWidth(498)
    listBg:SetHeight(322)
    listBg:SetBackdrop({
        bgFile = "Interface\\Tooltips\\UI-Tooltip-Background",
        edgeFile = "Interface\\Tooltips\\UI-Tooltip-Border",
        tile = true, tileSize = 16, edgeSize = 16,
        insets = { left = 3, right = 3, top = 3, bottom = 3 },
    })
    listBg:SetBackdropColor(0, 0, 0, 0.4)

    local scrollFrame = CreateFrame("ScrollFrame", "GuildBankViewerScrollFrame", listBg, "FauxScrollFrameTemplate")
    scrollFrame:SetPoint("TOPLEFT", listBg, "TOPLEFT", 0, -8)
    scrollFrame:SetWidth(468)
    scrollFrame:SetHeight(306)
    scrollFrame:SetScript("OnVerticalScroll", function()
        FauxScrollFrame_OnVerticalScroll(ITEM_ROW_HEIGHT, function() GuildBankViewer_RefreshList() end)
    end)

    for i = 1, MAX_NUM_ROWS do
        rows[i] = CreateRow(listBg, i)
    end

    -- Footer box: holds either the "no data yet" message or the per-alt
    -- gold tracker rows. Previously these sat directly on bankPage with no
    -- background of their own, so they visually spilled out past the
    -- list's bordered box instead of looking like a contained part of the
    -- window. Giving them a matching backdrop keeps everything inside a
    -- clean edge, and its height is kept in sync with the list's in
    -- UpdateBankListSize below.
    local footerBg = CreateFrame("Frame", nil, bankPage)
    footerBg:SetPoint("TOP", listBg, "BOTTOM", 0, -10)
    footerBg:SetWidth(498)
    footerBg:SetHeight(26)
    footerBg:SetBackdrop({
        bgFile = "Interface\\Tooltips\\UI-Tooltip-Background",
        edgeFile = "Interface\\Tooltips\\UI-Tooltip-Border",
        tile = true, tileSize = 16, edgeSize = 16,
        insets = { left = 3, right = 3, top = 3, bottom = 3 },
    })
    footerBg:SetBackdropColor(0, 0, 0, 0.4)
    f.footerBg = footerBg

    local bankFooter = footerBg:CreateFontString(nil, "OVERLAY", "GameFontDisableSmall")
    bankFooter:SetPoint("CENTER", footerBg, "CENTER", 0, 0)
    bankFooter:SetWidth(480)
    bankFooter:SetText("")
    f.bankFooter = bankFooter

    -- Gold tracker: real coin icons (gold/silver/copper), one row per bank alt.
    local altMoneyRows = {}
    for i = 1, MAX_ALT_MONEY_ROWS do
        local mrow = CreateFrame("Frame", nil, footerBg)
        mrow:SetWidth(300)
        mrow:SetHeight(20)
        if i == 1 then
            mrow:SetPoint("TOP", footerBg, "TOP", 0, -6)
        else
            mrow:SetPoint("TOP", altMoneyRows[i - 1].row, "BOTTOM", 0, -2)
        end

        local label = mrow:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
        label:SetPoint("RIGHT", mrow, "CENTER", -6, 0)
        label:SetWidth(130)
        label:SetJustifyH("RIGHT")

        local moneyFrame = CreateFrame("Frame", "GuildBankViewerAltMoney" .. i, mrow, "SmallMoneyFrameTemplate")
        moneyFrame:SetPoint("LEFT", mrow, "CENTER", 6, 0)
        -- SmallMoneyFrameTemplate defaults to Blizzard's "PLAYER" money
        -- type, which registers PLAYER_MONEY and silently overwrites
        -- whatever MoneyFrame_Update last set with the player's own
        -- GetMoney() the next time it fires -- e.g. after a vendor
        -- purchase or looting gold. That's what was showing your own
        -- money here instead of the bank alt's, until something (like
        -- switching tabs) called MoneyFrame_Update again. "STATIC" opts
        -- the frame out of that auto-refresh entirely, so it only ever
        -- shows what we explicitly set.
        moneyFrame.moneyType = "STATIC"

        mrow:Hide()
        altMoneyRows[i] = { row = mrow, label = label, moneyFrame = moneyFrame }
    end
    f.altMoneyRows = altMoneyRows

    -- The list above always starts at the same spot, but how much space is
    -- left below it (before the gold tracker + bottom border) depends on how
    -- many bank alts are synced. Grow/shrink the list to eat that leftover
    -- space instead of leaving it as dead backdrop.
    local function UpdateBankListSize()
        local moneyAreaHeight
        if bankFooter:IsShown() then
            moneyAreaHeight = 16
        else
            local shown = 0
            for i = 1, MAX_ALT_MONEY_ROWS do
                if altMoneyRows[i].row:IsShown() then shown = shown + 1 end
            end
            moneyAreaHeight = (shown > 0) and (shown * 20 + (shown - 1) * 2) or 16
        end

        -- 12px = 6px of breathing room above and below the content inside
        -- the footer box, so the text/coins don't touch its border.
        local footerBoxHeight = moneyAreaHeight + 12
        footerBg:SetHeight(footerBoxHeight)

        local available = 596 - 141 - 10 - footerBoxHeight - 20
        local visibleRows = 8
        for n = 8, MAX_NUM_ROWS do
            if ListContentHeight(n) <= available then
                visibleRows = n
            else
                break
            end
        end

        NUM_ROWS = visibleRows
        listBg:SetHeight(ListContentHeight(visibleRows))
        scrollFrame:SetHeight(RowsSpanHeight(visibleRows))
        GuildBankViewer_RefreshList()
    end

    ------------------------------------------------------------------
    -- Page: Selling
    ------------------------------------------------------------------

    local sellPage = CreateFrame("Frame", nil, f)
    sellPage:SetAllPoints(f)
    sellPage:Hide()

    local sellSearchLabel = sellPage:CreateFontString(nil, "OVERLAY", "GameFontNormal")
    sellSearchLabel:SetPoint("TOPLEFT", sellPage, "TOPLEFT", 20, -98)
    sellSearchLabel:SetText("Search:")

    local sellSearchBox = CreateFrame("EditBox", "GuildBankViewerSellSearchBox", sellPage, "InputBoxTemplate")
    sellSearchBox:SetWidth(160)
    sellSearchBox:SetHeight(20)
    sellSearchBox:SetPoint("LEFT", sellSearchLabel, "RIGHT", 10, 0)
    sellSearchBox:SetAutoFocus(false)
    sellSearchBox:SetScript("OnTextChanged", function() GuildBankViewer_RefreshSelling() end)
    sellSearchBox:SetScript("OnEscapePressed", function() this:ClearFocus() end)

    local newSellBtn = CreateFrame("Button", nil, sellPage, "UIPanelButtonTemplate")
    newSellBtn:SetWidth(110)
    newSellBtn:SetHeight(22)
    newSellBtn:SetPoint("TOPRIGHT", sellPage, "TOPRIGHT", -20, -95)
    newSellBtn:SetText("New Listing")
    newSellBtn:SetScript("OnClick", function()
        GuildBankViewer_OpenNewSelling()
    end)

    MakeSortHeader("sell", sellPage, "name", "Item", 50, -125, 148, "Click to sort alphabetically.\nRight-click to sort by rarity.", true)
    MakeSortHeader("sell", sellPage, "qty", "Qty", 204, -125, 34)
    MakeSortHeader("sell", sellPage, "amount", "Price", 240, -125, 70)
    MakeSortHeader("sell", sellPage, "poster", "Seller", 316, -125, 90)
    GuildBankViewer_UpdateSortHeaders("sell")

    local sellListBg = CreateFrame("Frame", nil, sellPage)
    sellListBg:SetPoint("TOPLEFT", sellPage, "TOPLEFT", 16, -141)
    sellListBg:SetWidth(498)
    sellListBg:SetHeight(ListContentHeight(MARKET_MAX_VISIBLE_ROWS))
    sellListBg:SetBackdrop({
        bgFile = "Interface\\Tooltips\\UI-Tooltip-Background",
        edgeFile = "Interface\\Tooltips\\UI-Tooltip-Border",
        tile = true, tileSize = 16, edgeSize = 16,
        insets = { left = 3, right = 3, top = 3, bottom = 3 },
    })
    sellListBg:SetBackdropColor(0, 0, 0, 0.4)

    local sellScrollFrame = CreateFrame("ScrollFrame", "GuildBankViewerSellScrollFrame", sellListBg, "FauxScrollFrameTemplate")
    sellScrollFrame:SetPoint("TOPLEFT", sellListBg, "TOPLEFT", 0, -8)
    sellScrollFrame:SetWidth(468)
    sellScrollFrame:SetHeight(RowsSpanHeight(MARKET_MAX_VISIBLE_ROWS))
    sellScrollFrame:SetScript("OnVerticalScroll", function()
        FauxScrollFrame_OnVerticalScroll(ITEM_ROW_HEIGHT, function() GuildBankViewer_RefreshSelling() end)
    end)

    for i = 1, MARKET_NUM_ROWS do
        sellingRows[i] = CreateMarketRow(sellListBg, i, sellingRows, "Sell")
    end

    local sellFooter = sellPage:CreateFontString(nil, "OVERLAY", "GameFontDisableSmall")
    sellFooter:SetPoint("TOP", sellListBg, "BOTTOM", 0, -10)
    sellFooter:SetWidth(500)
    sellFooter:SetText("Anyone can list consumables here. Whisper a seller to arrange the trade in person.")

    ------------------------------------------------------------------
    -- Page: Bounties
    ------------------------------------------------------------------

    local bountyPage = CreateFrame("Frame", nil, f)
    bountyPage:SetAllPoints(f)
    bountyPage:Hide()

    local bountySearchLabel = bountyPage:CreateFontString(nil, "OVERLAY", "GameFontNormal")
    bountySearchLabel:SetPoint("TOPLEFT", bountyPage, "TOPLEFT", 20, -98)
    bountySearchLabel:SetText("Search:")

    local bountySearchBox = CreateFrame("EditBox", "GuildBankViewerBountySearchBox", bountyPage, "InputBoxTemplate")
    bountySearchBox:SetWidth(160)
    bountySearchBox:SetHeight(20)
    bountySearchBox:SetPoint("LEFT", bountySearchLabel, "RIGHT", 10, 0)
    bountySearchBox:SetAutoFocus(false)
    bountySearchBox:SetScript("OnTextChanged", function() GuildBankViewer_RefreshBounties() end)
    bountySearchBox:SetScript("OnEscapePressed", function() this:ClearFocus() end)

    local newBountyBtn = CreateFrame("Button", nil, bountyPage, "UIPanelButtonTemplate")
    newBountyBtn:SetWidth(110)
    newBountyBtn:SetHeight(22)
    newBountyBtn:SetPoint("TOPRIGHT", bountyPage, "TOPRIGHT", -20, -95)
    newBountyBtn:SetText("New Bounty")
    newBountyBtn:SetScript("OnClick", function()
        GuildBankViewer_OpenNewBounty()
    end)

    MakeSortHeader("bounty", bountyPage, "name", "Item", 50, -125, 148, "Click to sort alphabetically.\nRight-click to sort by rarity.", true)
    MakeSortHeader("bounty", bountyPage, "qty", "Qty", 204, -125, 34)
    MakeSortHeader("bounty", bountyPage, "amount", "Reward", 240, -125, 70)
    MakeSortHeader("bounty", bountyPage, "poster", "Poster", 316, -125, 90)
    GuildBankViewer_UpdateSortHeaders("bounty")

    local bountyListBg = CreateFrame("Frame", nil, bountyPage)
    bountyListBg:SetPoint("TOPLEFT", bountyPage, "TOPLEFT", 16, -141)
    bountyListBg:SetWidth(498)
    bountyListBg:SetHeight(ListContentHeight(MARKET_MAX_VISIBLE_ROWS))
    bountyListBg:SetBackdrop({
        bgFile = "Interface\\Tooltips\\UI-Tooltip-Background",
        edgeFile = "Interface\\Tooltips\\UI-Tooltip-Border",
        tile = true, tileSize = 16, edgeSize = 16,
        insets = { left = 3, right = 3, top = 3, bottom = 3 },
    })
    bountyListBg:SetBackdropColor(0, 0, 0, 0.4)

    local bountyScrollFrame = CreateFrame("ScrollFrame", "GuildBankViewerBountyScrollFrame", bountyListBg, "FauxScrollFrameTemplate")
    bountyScrollFrame:SetPoint("TOPLEFT", bountyListBg, "TOPLEFT", 0, -8)
    bountyScrollFrame:SetWidth(468)
    bountyScrollFrame:SetHeight(RowsSpanHeight(MARKET_MAX_VISIBLE_ROWS))
    bountyScrollFrame:SetScript("OnVerticalScroll", function()
        FauxScrollFrame_OnVerticalScroll(ITEM_ROW_HEIGHT, function() GuildBankViewer_RefreshBounties() end)
    end)

    for i = 1, MARKET_NUM_ROWS do
        bountyRows[i] = CreateMarketRow(bountyListBg, i, bountyRows, "Bounty")
    end

    local bountyFooter = bountyPage:CreateFontString(nil, "OVERLAY", "GameFontDisableSmall")
    bountyFooter:SetPoint("TOP", bountyListBg, "BOTTOM", 0, -10)
    bountyFooter:SetWidth(500)
    bountyFooter:SetText("Post what you need and what you're paying. Whisper a poster to fulfill their bounty.")

    ------------------------------------------------------------------
    -- Tab switching
    ------------------------------------------------------------------

    -- Rebuilds the "<alt>: <gold>" rows at the bottom of the Bank tab.
    -- Pulled out of ShowTab so it can also be called from outside (e.g.
    -- after a FORGET removes an alt) without forcing the window onto the
    -- Bank tab if the person is looking at Selling/Bounties.
    local function RefreshBankAltRows()
        local altNames = {}
        local myGuild = CurrentGuildKey()
        for altName, data in pairs(GuildBankViewerDB.banks) do
            if myGuild and data.guild == myGuild then
                table.insert(altNames, altName)
            end
        end
        table.sort(altNames)

        if table.getn(altNames) == 0 then
            f.bankFooter:SetText("No bank data received yet. Have the bank alt open its bank.")
            f.bankFooter:Show()
            for i = 1, MAX_ALT_MONEY_ROWS do
                altMoneyRows[i].row:Hide()
            end
        else
            f.bankFooter:Hide()
            for i = 1, MAX_ALT_MONEY_ROWS do
                local altName = altNames[i]
                if altName then
                    local row = altMoneyRows[i]
                    row.label:SetText(altName .. ":")
                    MoneyFrame_Update(row.moneyFrame:GetName(), GuildBankViewerDB.banks[altName].gold or 0)

                    -- Re-center this label+money pair as a unit: a fixed
                    -- split point looks centered only when the label and the
                    -- money display happen to be the same width, which they
                    -- almost never are (alt names vary, and gold/silver/copper
                    -- digit counts vary too).
                    local gap = 8
                    local labelWidth = row.label:GetStringWidth()
                    local moneyWidth = row.moneyFrame:GetWidth()
                    local half = (labelWidth + gap + moneyWidth) / 2
                    row.label:ClearAllPoints()
                    row.label:SetPoint("RIGHT", row.row, "CENTER", labelWidth - half, 0)
                    row.moneyFrame:ClearAllPoints()
                    row.moneyFrame:SetPoint("LEFT", row.row, "CENTER", half - moneyWidth, 0)

                    altMoneyRows[i].row:Show()
                else
                    altMoneyRows[i].row:Hide()
                end
            end
        end
        UpdateBankListSize()
    end
    f.RefreshBankAltRows = RefreshBankAltRows

    local function ShowTab(which)
        f.activeTab = which
        bankPage:Hide()
        sellPage:Hide()
        bountyPage:Hide()
        tabBank:Enable()
        tabSell:Enable()
        tabBounty:Enable()

        if which == "bank" then
            bankPage:Show()
            tabBank:Disable()
            GuildBankViewer_RefreshList()
            RefreshBankAltRows()
        elseif which == "sell" then
            sellPage:Show()
            tabSell:Disable()
            GuildBankViewer_RefreshSelling()
            if IsOfficer(UnitName("player")) then
                newSellBtn:Show()
                sellFooter:SetText("These are the guild bank's own listings. Whisper a seller to arrange the trade in person.")
            else
                newSellBtn:Hide()
                sellFooter:SetText("These are the guild bank's listings, posted by officers. Whisper a seller to buy.")
            end
        elseif which == "bounty" then
            bountyPage:Show()
            tabBounty:Disable()
            GuildBankViewer_RefreshBounties()
            if IsOfficer(UnitName("player")) then
                newBountyBtn:Show()
                bountyFooter:SetText("These are the guild bank's own bounties. Whisper a poster to fulfill one.")
            else
                newBountyBtn:Hide()
                bountyFooter:SetText("These are the guild bank's bounties, posted by officers. Whisper a poster to fulfill one.")
            end
        end
    end

    tabBank:SetScript("OnClick", function() ShowTab("bank") end)
    tabSell:SetScript("OnClick", function() ShowTab("sell") end)
    tabBounty:SetScript("OnClick", function() ShowTab("bounty") end)

    f:SetScript("OnShow", function()
        ShowTab("bank")
    end)

    return f
end

----------------------------------------------------------------------
-- UI: ticket window
----------------------------------------------------------------------

local TICKET_NUM_ROWS = 12
local ticketRows = {}
local sortedTickets = {}

local function BuildTickets()
    sortedTickets = {}
    local iAmOfficer = IsOfficer(UnitName("player"))
    local myGuild = CurrentGuildKey()
    for ticketID, t in pairs(GuildBankViewerDB.tickets) do
        if myGuild and t.guild == myGuild and (iAmOfficer or t.requester == UnitName("player")) then
            table.insert(sortedTickets, { id = ticketID, data = t })
        end
    end
    table.sort(sortedTickets, function(a, b) return a.data.ts > b.data.ts end)
end

function GuildBankViewer_RefreshTickets()
    BuildTickets()

    local offset = FauxScrollFrame_GetOffset(GuildBankViewerTicketScrollFrame) or 0
    FauxScrollFrame_Update(GuildBankViewerTicketScrollFrame, table.getn(sortedTickets), TICKET_NUM_ROWS, ROW_HEIGHT)

    for i = 1, TICKET_NUM_ROWS do
        local row = ticketRows[i]
        local dataIndex = i + offset
        local entry = sortedTickets[dataIndex]
        if entry then
            local t = entry.data
            row.item:SetText(t.qty .. "x " .. t.itemName)
            row.requester:SetText(t.requester)
            row.alt:SetText(t.altName)
            row.status:SetText(t.status)
            row.ticketID = entry.id

            if IsOfficer(UnitName("player")) and t.status == "pending" then
                row.approveBtn:Show()
                row.denyBtn:Show()
            else
                row.approveBtn:Hide()
                row.denyBtn:Hide()
            end
            row:Show()
        else
            row:Hide()
        end
    end
end

local function CreateTicketRow(parent, index)
    local row = CreateFrame("Frame", "GuildBankViewerTicketRow" .. index, parent)
    row:SetHeight(ROW_HEIGHT)
    row:SetWidth(520)
    if index == 1 then
        row:SetPoint("TOPLEFT", parent, "TOPLEFT", 8, -8)
    else
        row:SetPoint("TOPLEFT", ticketRows[index - 1], "BOTTOMLEFT", 0, 0)
    end

    row.item = row:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    row.item:SetPoint("LEFT", row, "LEFT", 0, 0)
    row.item:SetWidth(145)
    row.item:SetJustifyH("LEFT")

    row.requester = row:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    row.requester:SetPoint("LEFT", row, "LEFT", 154, 0)
    row.requester:SetWidth(70)
    row.requester:SetJustifyH("LEFT")

    row.alt = row:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    row.alt:SetPoint("LEFT", row, "LEFT", 228, 0)
    row.alt:SetWidth(55)
    row.alt:SetJustifyH("LEFT")

    row.status = row:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    row.status:SetPoint("LEFT", row, "LEFT", 287, 0)
    row.status:SetWidth(75)
    row.status:SetJustifyH("LEFT")

    local approveBtn = CreateFrame("Button", "GuildBankViewerTicketRow" .. index .. "Approve", row, "UIPanelButtonTemplate")
    approveBtn:SetWidth(66)
    approveBtn:SetHeight(16)
    approveBtn:SetPoint("LEFT", row, "LEFT", 366, 0)
    approveBtn:SetText("Approve")
    getglobal(approveBtn:GetName() .. "Text"):SetFontObject("GameFontNormalSmall")
    approveBtn:SetScript("OnClick", function()
        ActOnTicket(row.ticketID, "approved")
    end)
    row.approveBtn = approveBtn

    local denyBtn = CreateFrame("Button", "GuildBankViewerTicketRow" .. index .. "Deny", row, "UIPanelButtonTemplate")
    denyBtn:SetWidth(50)
    denyBtn:SetHeight(16)
    denyBtn:SetPoint("LEFT", approveBtn, "RIGHT", 4, 0)
    denyBtn:SetText("Deny")
    getglobal(denyBtn:GetName() .. "Text"):SetFontObject("GameFontNormalSmall")
    denyBtn:SetScript("OnClick", function()
        ActOnTicket(row.ticketID, "denied")
    end)
    row.denyBtn = denyBtn

    return row
end

local function CreateTicketFrame()
    local f = CreateFrame("Frame", "GuildBankViewerTicketFrame", UIParent)
    f:SetWidth(560)
    f:SetHeight(340)
    f:SetPoint("CENTER", UIParent, "CENTER", 0, -40)
    f:SetFrameStrata("DIALOG")
    f:SetBackdrop({
        bgFile = "Interface\\DialogFrame\\UI-DialogBox-Background",
        edgeFile = "Interface\\DialogFrame\\UI-DialogBox-Border",
        tile = true, tileSize = 32, edgeSize = 32,
        insets = { left = 11, right = 12, top = 12, bottom = 11 },
    })
    f:SetMovable(true)
    f:EnableMouse(true)
    f:RegisterForDrag("LeftButton")
    f:SetScript("OnDragStart", function() this:StartMoving() end)
    f:SetScript("OnDragStop", function() this:StopMovingOrSizing() end)
    f:Hide()

    local title = f:CreateFontString(nil, "OVERLAY", "GameFontNormalLarge")
    title:SetPoint("TOP", f, "TOP", 0, -16)
    title:SetText("Guild Bank Requests")

    local closeBtn = CreateFrame("Button", nil, f, "UIPanelCloseButton")
    closeBtn:SetPoint("TOPRIGHT", f, "TOPRIGHT", -5, -5)

    local h1 = f:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    h1:SetPoint("TOPLEFT", f, "TOPLEFT", 28, -50)
    h1:SetText("Item")

    local h2 = f:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    h2:SetPoint("TOPLEFT", f, "TOPLEFT", 178, -50)
    h2:SetText("Requester")

    local h3 = f:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    h3:SetPoint("TOPLEFT", f, "TOPLEFT", 252, -50)
    h3:SetText("Alt")

    local h4 = f:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    h4:SetPoint("TOPLEFT", f, "TOPLEFT", 311, -50)
    h4:SetText("Status")

    local listBg = CreateFrame("Frame", nil, f)
    listBg:SetPoint("TOPLEFT", f, "TOPLEFT", 16, -66)
    listBg:SetWidth(528)
    listBg:SetHeight(232)
    listBg:SetBackdrop({
        bgFile = "Interface\\Tooltips\\UI-Tooltip-Background",
        edgeFile = "Interface\\Tooltips\\UI-Tooltip-Border",
        tile = true, tileSize = 16, edgeSize = 16,
        insets = { left = 3, right = 3, top = 3, bottom = 3 },
    })
    listBg:SetBackdropColor(0, 0, 0, 0.4)

    local scrollFrame = CreateFrame("ScrollFrame", "GuildBankViewerTicketScrollFrame", listBg, "FauxScrollFrameTemplate")
    scrollFrame:SetPoint("TOPLEFT", listBg, "TOPLEFT", 0, -8)
    scrollFrame:SetWidth(520)
    scrollFrame:SetHeight(216)
    scrollFrame:SetScript("OnVerticalScroll", function()
        FauxScrollFrame_OnVerticalScroll(ROW_HEIGHT, function() GuildBankViewer_RefreshTickets() end)
    end)

    for i = 1, TICKET_NUM_ROWS do
        ticketRows[i] = CreateTicketRow(listBg, i)
    end

    local footer = f:CreateFontString(nil, "OVERLAY", "GameFontDisableSmall")
    footer:SetPoint("BOTTOM", f, "BOTTOM", 0, 16)
    f.footer = footer

    f:SetScript("OnShow", function()
        RefreshGuildRoster()
        GuildBankViewer_RefreshTickets()
        if IsOfficer(UnitName("player")) then
            title:SetText("Guild Bank Requests")
            f.footer:SetText("You can approve/deny requests here.")
        else
            title:SetText("My Requests")
            f.footer:SetText("Showing only your own requests. Officers see and manage everyone's.")
        end
    end)

    return f
end

----------------------------------------------------------------------
-- UI: settings window (bank alt / officer / minimap toggles)
----------------------------------------------------------------------

local function CreateSettingsFrame()
    local f = CreateFrame("Frame", "GuildBankViewerSettingsFrame", UIParent)
    f:SetWidth(340)
    f:SetHeight(320)
    f:SetPoint("CENTER", UIParent, "CENTER", 0, 60)
    f:SetFrameStrata("DIALOG")
    f:SetBackdrop({
        bgFile = "Interface\\DialogFrame\\UI-DialogBox-Background",
        edgeFile = "Interface\\DialogFrame\\UI-DialogBox-Border",
        tile = true, tileSize = 32, edgeSize = 32,
        insets = { left = 11, right = 12, top = 12, bottom = 11 },
    })
    f:SetMovable(true)
    f:EnableMouse(true)
    f:RegisterForDrag("LeftButton")
    f:SetScript("OnDragStart", function() this:StartMoving() end)
    f:SetScript("OnDragStop", function() this:StopMovingOrSizing() end)
    f:Hide()

    local title = f:CreateFontString(nil, "OVERLAY", "GameFontNormalLarge")
    title:SetPoint("TOP", f, "TOP", 0, -16)
    title:SetText("Guild Bank Viewer Settings")

    local closeBtn = CreateFrame("Button", nil, f, "UIPanelCloseButton")
    closeBtn:SetPoint("TOPRIGHT", f, "TOPRIGHT", -5, -5)

    local charLabel = f:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    charLabel:SetPoint("TOPLEFT", f, "TOPLEFT", 20, -45)
    charLabel:SetText("This character (" .. UnitName("player") .. "):")

    local altCheck = CreateFrame("CheckButton", "GuildBankViewerAltCheck", f, "UICheckButtonTemplate")
    altCheck:SetPoint("TOPLEFT", f, "TOPLEFT", 16, -65)
    getglobal(altCheck:GetName() .. "Text"):SetText("This is a bank alt (auto-sync its bank)")
    altCheck:SetScript("OnClick", function()
        GuildBankViewerCharDB.isBankAlt = (this:GetChecked() == 1)
        if GuildBankViewerCharDB.isBankAlt then
            Print("Will sync this character's bank to the guild whenever it's opened.")
        else
            Print("This character will no longer sync its bank.")
            -- Tell the whole guild to drop this alt's data too -- otherwise
            -- it just sits in everyone's cache forever, and other members'
            -- clients will keep relaying it as if it were still current.
            ForgetBankAlt(UnitName("player"))
        end
    end)
    f.altCheck = altCheck

    -- Officer status is read-only here: it's derived from the character's
    -- REAL guild rank (fetched from the server), not something you can tick.
    local rankLabel = f:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    rankLabel:SetPoint("TOPLEFT", altCheck, "BOTTOMLEFT", 0, -14)
    rankLabel:SetWidth(300)
    rankLabel:SetJustifyH("LEFT")
    f.rankLabel = rankLabel

    local thresholdLabel = f:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    thresholdLabel:SetPoint("TOPLEFT", rankLabel, "BOTTOMLEFT", 0, -10)
    thresholdLabel:SetText("Officer rank cutoff (0 = top rank):")

    local thresholdBox = CreateFrame("EditBox", "GuildBankViewerThresholdBox", f, "InputBoxTemplate")
    thresholdBox:SetWidth(35)
    thresholdBox:SetHeight(18)
    thresholdBox:SetPoint("LEFT", thresholdLabel, "RIGHT", 10, 0)
    thresholdBox:SetAutoFocus(false)
    thresholdBox:SetNumeric(true)
    thresholdBox:SetMaxLetters(2)
    local function ApplyThreshold()
        local v = tonumber(thresholdBox:GetText())
        if not v or v < 0 then v = 1 end
        GuildBankViewerDB.officerRankThreshold = v
        thresholdBox:SetText(tostring(v))
        GuildBankViewer_RefreshSettingsRankInfo()
    end
    thresholdBox:SetScript("OnEnterPressed", function() ApplyThreshold() this:ClearFocus() end)
    thresholdBox:SetScript("OnEditFocusLost", ApplyThreshold)
    f.thresholdBox = thresholdBox

    local thresholdHint = f:CreateFontString(nil, "OVERLAY", "GameFontDisableSmall")
    thresholdHint:SetPoint("TOPLEFT", thresholdLabel, "BOTTOMLEFT", 0, -4)
    thresholdHint:SetWidth(300)
    thresholdHint:SetJustifyH("LEFT")
    thresholdHint:SetText("Keep this the same across your guild -- ranks at or above this cutoff can approve/deny requests. Default (1) covers Guild Master + the next rank down.")

    local minimapCheck = CreateFrame("CheckButton", "GuildBankViewerMinimapCheck", f, "UICheckButtonTemplate")
    minimapCheck:SetPoint("TOPLEFT", thresholdHint, "BOTTOMLEFT", -4, -18)
    getglobal(minimapCheck:GetName() .. "Text"):SetText("Show minimap icon")
    minimapCheck:SetScript("OnClick", function()
        GuildBankViewerDB.minimapHidden = (this:GetChecked() ~= 1)
        GuildBankViewer_UpdateMinimapVisibility()
    end)
    f.minimapCheck = minimapCheck

    local syncBtn = CreateFrame("Button", "GuildBankViewerSyncBtn", f, "UIPanelButtonTemplate")
    syncBtn:SetWidth(130)
    syncBtn:SetHeight(22)
    syncBtn:SetPoint("TOPLEFT", minimapCheck, "BOTTOMLEFT", 4, -16)
    syncBtn:SetText("Sync Now")
    syncBtn:SetScript("OnClick", function()
        if GuildBankViewerCharDB.isBankAlt then
            lastBroadcastSignature = nil
            BroadcastBankData(true)
            Print("Manual sync sent to guild.")
        else
            Print("Check \"This is a bank alt\" above first.")
        end
    end)

    function GuildBankViewer_RefreshSettingsRankInfo()
        local myName = UnitName("player")
        local info = guildRankOf[myName]
        if info then
            local status = IsOfficer(myName) and "|cff33ff99Officer|r" or "Member"
            rankLabel:SetText("Your guild rank: " .. info.title .. "  (" .. status .. ")")
        else
            rankLabel:SetText("Your guild rank: unknown (waiting on guild roster...)")
        end
    end

    f:SetScript("OnShow", function()
        f.altCheck:SetChecked(GuildBankViewerCharDB.isBankAlt)
        f.minimapCheck:SetChecked(not GuildBankViewerDB.minimapHidden)
        f.thresholdBox:SetText(tostring(GetOfficerThreshold()))
        RefreshGuildRoster()
        GuildBankViewer_RefreshSettingsRankInfo()
    end)

    return f
end

----------------------------------------------------------------------
-- UI: "New Listing" / "New Bounty" popup (drag an item, set qty + price)
----------------------------------------------------------------------

local function CreateNewMarketEntryFrame(kind, titleText, actionText)
    local frameName = "GuildBankViewerNew" .. kind .. "Frame"
    local f = CreateFrame("Frame", frameName, UIParent)
    f:SetWidth(320)
    f:SetHeight(360)
    f:SetPoint("CENTER", UIParent, "CENTER", 0, 0)
    f:SetFrameStrata("DIALOG")
    f:SetBackdrop({
        bgFile = "Interface\\DialogFrame\\UI-DialogBox-Background",
        edgeFile = "Interface\\DialogFrame\\UI-DialogBox-Border",
        tile = true, tileSize = 32, edgeSize = 32,
        insets = { left = 11, right = 12, top = 12, bottom = 11 },
    })
    f:SetMovable(true)
    f:EnableMouse(true)
    f:RegisterForDrag("LeftButton")
    f:SetScript("OnDragStart", function() this:StartMoving() end)
    f:SetScript("OnDragStop", function() this:StopMovingOrSizing() end)
    f:Hide()

    local title = f:CreateFontString(nil, "OVERLAY", "GameFontNormalLarge")
    title:SetPoint("TOP", f, "TOP", 0, -16)
    title:SetText(titleText)

    local closeBtn = CreateFrame("Button", nil, f, "UIPanelCloseButton")
    closeBtn:SetPoint("TOPRIGHT", f, "TOPRIGHT", -5, -5)

    -- Item slot: drag an item from your bags onto this
    local slot = CreateFrame("Button", frameName .. "ItemSlot", f)
    slot:SetWidth(37)
    slot:SetHeight(37)
    slot:SetPoint("TOPLEFT", f, "TOPLEFT", 24, -46)
    slot:SetNormalTexture("Interface\\PaperDoll\\UI-Backpack-EmptySlot")
    slot:RegisterForClicks("LeftButtonUp")
    slot:RegisterForDrag("LeftButton")

    -- Previously used ARTWORK layer + sublevel 1 to draw above the slot's
    -- own SetNormalTexture backpack-slot art (also ARTWORK, sublevel 0).
    -- That still wasn't reliably winning on this client, so use the
    -- "OVERLAY" layer instead -- layers have a fixed, unconditional
    -- stacking order (BACKGROUND < BORDER < ARTWORK < OVERLAY <
    -- HIGHLIGHT) that doesn't depend on sublevel or creation-order
    -- quirks the way same-layer sublevels apparently do here.
    local icon = slot:CreateTexture(nil, "OVERLAY")
    icon:SetAllPoints(slot)
    icon:Hide()
    slot.icon = icon

    local selectedLabel = f:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    selectedLabel:SetPoint("LEFT", slot, "RIGHT", 10, 0)
    selectedLabel:SetWidth(220)
    selectedLabel:SetJustifyH("LEFT")
    selectedLabel:SetText("Drag an item, or search below")

    -- Items picked from search (or dragged items the client hasn't fully
    -- cached yet) can return a nil texture from GetItemIcon on the first
    -- call, since the item's data hasn't finished loading from the server.
    -- Poll for a few seconds until it becomes available.
    local iconRetry = CreateFrame("Frame", frameName .. "IconRetry", UIParent)
    iconRetry:Hide()
    local iconRetryItemID, iconRetryElapsed, iconRetryAttempts

    iconRetry:SetScript("OnUpdate", function()
        if not iconRetryItemID then
            this:Hide()
            return
        end
        iconRetryElapsed = (iconRetryElapsed or 0) + arg1
        if iconRetryElapsed < 0.2 then return end
        iconRetryElapsed = 0
        iconRetryAttempts = (iconRetryAttempts or 0) + 1

        local texture = SafeGetItemIcon(iconRetryItemID)
        if texture then
            icon:SetTexture(texture)
            icon:Show()
            iconRetryItemID = nil
            this:Hide()
        elseif iconRetryAttempts >= 20 then
            -- Give up after ~4 seconds; item data never arrived.
            iconRetryItemID = nil
            this:Hide()
        end
    end)

    local function SelectItem(itemID, name, link, texture)
        f.selectedItemID = itemID
        f.selectedItemName = name
        f.selectedItemLink = link
        if texture then
            icon:SetTexture(texture)
            icon:Show()
            iconRetryItemID = nil
            iconRetry:Hide()
        else
            -- Don't just hide the icon while we wait/retry (or if
            -- resolution never succeeds) -- show the generic placeholder
            -- so the slot never sits blank, same as the main list does.
            icon:SetTexture(ICON_PLACEHOLDER)
            icon:Show()
            if itemID then
                iconRetryItemID = itemID
                iconRetryElapsed = 0
                iconRetryAttempts = 0
                iconRetry:Show()
            end
        end
        selectedLabel:SetText(name or ("Item #" .. itemID))
    end

    local function ClearSelection()
        f.selectedItemID = nil
        f.selectedItemName = nil
        f.selectedItemLink = nil
        icon:Hide()
        iconRetryItemID = nil
        iconRetry:Hide()
        selectedLabel:SetText("Drag an item, or search below")
    end

    local function TakeDraggedSelection()
        if pendingDragItem then
            local name = GetItemInfo(pendingDragItem.itemID)
            local texture = SafeGetItemIcon(pendingDragItem.itemID)
            SelectItem(pendingDragItem.itemID, name, pendingDragItem.link, texture)
            ClearCursor()
        end
    end

    slot:SetScript("OnReceiveDrag", TakeDraggedSelection)
    slot:SetScript("OnClick", function()
        if CursorHasItem() then
            TakeDraggedSelection()
        else
            ClearSelection()
        end
    end)
    slot:SetScript("OnEnter", function()
        if f.selectedItemLink then
            GameTooltip:SetOwner(this, "ANCHOR_CURSOR")
            GameTooltip:SetHyperlink(f.selectedItemLink)
            GameTooltip:Show()
        end
    end)
    slot:SetScript("OnLeave", function()
        GameTooltip:Hide()
    end)

    ------------------------------------------------------------------
    -- Search box: searches every item this account has ever seen
    -- (learned automatically -- see the knownItems system above), so
    -- you don't have to physically hold the item to list/bounty it.
    ------------------------------------------------------------------

    local searchLabel = f:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    searchLabel:SetPoint("TOPLEFT", slot, "BOTTOMLEFT", 0, -14)
    searchLabel:SetText("Or search known items:")

    local searchBox = CreateFrame("EditBox", frameName .. "SearchBox", f, "InputBoxTemplate")
    searchBox:SetWidth(250)
    searchBox:SetHeight(20)
    searchBox:SetPoint("TOPLEFT", searchLabel, "BOTTOMLEFT", 4, -6)
    searchBox:SetAutoFocus(false)
    searchBox:SetScript("OnEscapePressed", function() this:ClearFocus() end)

    local NUM_RESULT_ROWS = 4
    local resultRows = {}
    local searchResults = {}

    for i = 1, NUM_RESULT_ROWS do
        local row = CreateFrame("Button", frameName .. "Result" .. i, f)
        row:SetWidth(270)
        row:SetHeight(16)
        if i == 1 then
            row:SetPoint("TOPLEFT", searchBox, "BOTTOMLEFT", 0, -4)
        else
            row:SetPoint("TOPLEFT", resultRows[i - 1], "BOTTOMLEFT", 0, 0)
        end
        row:SetHighlightTexture("Interface\\QuestFrame\\UI-QuestTitleHighlight")

        local rowIcon = row:CreateTexture(nil, "ARTWORK")
        rowIcon:SetWidth(14)
        rowIcon:SetHeight(14)
        rowIcon:SetPoint("LEFT", row, "LEFT", 0, 0)
        row.icon = rowIcon

        local text = row:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
        text:SetPoint("LEFT", row, "LEFT", 18, 0)
        text:SetPoint("RIGHT", row, "RIGHT", 0, 0)
        text:SetJustifyH("LEFT")
        row.text = text
        row:Hide()
        resultRows[i] = row
    end

    local function RefreshSearchResults()
        local query = string.lower(searchBox:GetText() or "")
        searchResults = {}
        if query ~= "" then
            local seen = {}
            -- Live-learned names take priority (guaranteed accurate for THIS item
            -- as this client has actually seen it) over the bundled DB fallback.
            for id, name in pairs(GuildBankViewerDB.knownItems) do
                if string.find(string.lower(name), query, 1, true) then
                    table.insert(searchResults, { id = id, name = name })
                    seen[id] = true
                end
            end
            if GBV_ItemDB and string.len(query) >= 3 then
                for id, name in pairs(GBV_ItemDB) do
                    if not seen[id] and string.find(string.lower(name), query, 1, true) then
                        table.insert(searchResults, { id = id, name = name })
                    end
                end
            end
            table.sort(searchResults, function(a, b) return a.name < b.name end)
        end

        for i = 1, NUM_RESULT_ROWS do
            local row = resultRows[i]
            local entry = searchResults[i]
            if entry then
                local r, g, b = 1, 1, 1
                local _, _, quality = GetItemInfo(entry.id)
                local texture = SafeGetItemIcon(entry.id)
                if quality and ITEM_QUALITY_COLORS and ITEM_QUALITY_COLORS[quality] then
                    local c = ITEM_QUALITY_COLORS[quality]
                    r, g, b = c.r, c.g, c.b
                end
                row.text:SetText(entry.name)
                row.text:SetTextColor(r, g, b)
                row.icon:SetTexture(SafeIconTexture(texture))
                row.itemID = entry.id
                row.itemName = entry.name
                row:Show()
            else
                row:Hide()
            end
        end
    end

    searchBox:SetScript("OnTextChanged", RefreshSearchResults)

    for i = 1, NUM_RESULT_ROWS do
        local row = resultRows[i]
        row:SetScript("OnClick", function()
            local name, link = GetItemInfo(row.itemID)
            local texture = SafeGetItemIcon(row.itemID)
            SelectItem(row.itemID, name or row.itemName, link or ("item:" .. row.itemID), texture)
            searchBox:SetText("")
            RefreshSearchResults()
        end)
        row:SetScript("OnEnter", function()
            GameTooltip:SetOwner(this, "ANCHOR_CURSOR")
            GameTooltip:SetHyperlink("item:" .. row.itemID)
            GameTooltip:Show()
        end)
        row:SetScript("OnLeave", function()
            GameTooltip:Hide()
        end)
    end

    local qtyLabel = f:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    qtyLabel:SetPoint("TOPLEFT", searchBox, "BOTTOMLEFT", 0, -92)
    qtyLabel:SetText("Qty:")

    local qtyBox = CreateFrame("EditBox", frameName .. "QtyBox", f, "InputBoxTemplate")
    qtyBox:SetWidth(40)
    qtyBox:SetHeight(20)
    qtyBox:SetPoint("LEFT", qtyLabel, "RIGHT", 10, 0)
    qtyBox:SetAutoFocus(false)
    qtyBox:SetNumeric(true)
    qtyBox:SetMaxLetters(4)
    qtyBox:SetText("1")

    local amountLabel = f:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    amountLabel:SetPoint("TOPLEFT", qtyLabel, "BOTTOMLEFT", 0, -18)
    amountLabel:SetText((kind == "SELL") and "Price:" or "Bounty:")

    local moneyFrame = CreateFrame("Frame", frameName .. "MoneyFrame", f, "MoneyInputFrameTemplate")
    moneyFrame:SetPoint("LEFT", amountLabel, "RIGHT", 8, 0)

    local postBtn = CreateFrame("Button", nil, f, "UIPanelButtonTemplate")
    postBtn:SetWidth(100)
    postBtn:SetHeight(22)
    postBtn:SetPoint("BOTTOM", f, "BOTTOM", -55, 16)
    postBtn:SetText(actionText)
    postBtn:SetScript("OnClick", function()
        if not f.selectedItemID then
            Print("Drag an item into the slot, or search and pick one, first.")
            return
        end
        local qty = tonumber(qtyBox:GetText()) or 1
        if qty < 1 then qty = 1 end
        local amount = MoneyInputFrame_GetCopper(moneyFrame) or 0
        local itemName = f.selectedItemName or GetItemInfo(f.selectedItemID) or ("Item #" .. f.selectedItemID)
        PostMarketEntry(kind, f.selectedItemID, itemName, qty, amount)
        f:Hide()
    end)

    local cancelBtn = CreateFrame("Button", nil, f, "UIPanelButtonTemplate")
    cancelBtn:SetWidth(80)
    cancelBtn:SetHeight(22)
    cancelBtn:SetPoint("LEFT", postBtn, "RIGHT", 8, 0)
    cancelBtn:SetText("Cancel")
    cancelBtn:SetScript("OnClick", function() f:Hide() end)

    f:SetScript("OnShow", function()
        ClearSelection()
        searchBox:SetText("")
        RefreshSearchResults()
        qtyBox:SetText("1")
        MoneyInputFrame_SetCopper(moneyFrame, 0)
    end)

    return f
end

function GuildBankViewer_OpenNewSelling()
    if not GuildBankViewerNewSELLFrame then
        CreateNewMarketEntryFrame("SELL", "Sell an Item", "List Item")
    end
    GuildBankViewerNewSELLFrame:Show()
end

function GuildBankViewer_OpenNewBounty()
    if not GuildBankViewerNewBOUNTYFrame then
        CreateNewMarketEntryFrame("BOUNTY", "Post a Bounty", "Post Bounty")
    end
    GuildBankViewerNewBOUNTYFrame:Show()
end

----------------------------------------------------------------------
-- Window toggle helpers (used by minimap icon and in-window buttons)
----------------------------------------------------------------------

function GuildBankViewer_OpenMain()
    if not GuildBankViewerFrame then
        CreateMainFrame()
    end
    if GuildBankViewerFrame:IsShown() then
        GuildBankViewerFrame:Hide()
    else
        GuildBankViewerFrame:Show()
    end
end

function GuildBankViewer_OpenTickets()
    if not GuildBankViewerTicketFrame then
        CreateTicketFrame()
    end
    if GuildBankViewerTicketFrame:IsShown() then
        GuildBankViewerTicketFrame:Hide()
    else
        GuildBankViewerTicketFrame:Show()
    end
end

function GuildBankViewer_OpenSettings()
    if not GuildBankViewerSettingsFrame then
        CreateSettingsFrame()
    end
    if GuildBankViewerSettingsFrame:IsShown() then
        GuildBankViewerSettingsFrame:Hide()
    else
        GuildBankViewerSettingsFrame:Show()
    end
end

----------------------------------------------------------------------
-- Request quantity popup
----------------------------------------------------------------------

StaticPopupDialogs["GUILDBANKVIEWER_REQUEST"] = {
    text = "Request how many %s?",
    button1 = "Request",
    button2 = "Cancel",
    hasEditBox = true,
    maxLetters = 5,
    OnShow = function()
        getglobal(this:GetName() .. "EditBox"):SetText("1")
        getglobal(this:GetName() .. "EditBox"):SetFocus()
    end,
    OnAccept = function()
        local editBox = getglobal(this:GetParent():GetName() .. "EditBox")
        local qty = tonumber(editBox:GetText()) or 1
        if qty < 1 then qty = 1 end
        RequestItem(GuildBankViewer_PendingItemID, GuildBankViewer_PendingItemName, qty, GuildBankViewer_PendingAltName)
    end,
    EditBoxOnEnterPressed = function()
        local qty = tonumber(this:GetText()) or 1
        if qty < 1 then qty = 1 end
        RequestItem(GuildBankViewer_PendingItemID, GuildBankViewer_PendingItemName, qty, GuildBankViewer_PendingAltName)
        this:GetParent():Hide()
    end,
    timeout = 0,
    whileDead = 1,
    hideOnEscape = 1,
}

----------------------------------------------------------------------
-- Slash command (kept only as a fallback if the minimap icon gets hidden;
-- everything else -- bank alt/officer flags, sync, tickets -- is in the
-- Settings/Tickets buttons inside the window itself)
----------------------------------------------------------------------

SLASH_GUILDBANKVIEWER1 = "/gbank"
SlashCmdList["GUILDBANKVIEWER"] = function(msg)
    msg = msg or ""
    local _, _, cmd, arg = string.find(msg, "^%s*(%a+)%s*(.-)%s*$")

    if cmd == "links" then
        -- Debug helper: print the raw item-link text for everything in this
        -- character's bags/bank, with the "|" escaped so the chat frame
        -- shows the literal string instead of rendering it as a clickable
        -- link. Used to verify exactly where the random-suffix field sits
        -- in this server's item links.
        local function dumpContainer(bagID, label)
            local slots = GetContainerNumSlots(bagID)
            if not slots or slots == 0 then return end
            for slot = 1, slots do
                local link = GetContainerItemLink(bagID, slot)
                if link then
                    Print(label .. " slot " .. slot .. ": " .. string.gsub(link, "|", "||"))
                end
            end
        end
        Print("Raw item links (paste these back for debugging):")
        for bagID = 0, 4 do dumpContainer(bagID, "Bag " .. bagID) end
        dumpContainer(-1, "Bank")
        for bagID = 5, 10 do dumpContainer(bagID, "Bank bag " .. bagID) end
        return
    end

    if cmd == "forget" and arg ~= "" then
        -- Manual cleanup for an alt that's gone for good (deleted, renamed,
        -- left the guild, etc.) and so can never self-retire by unchecking
        -- its own "bank alt" box. Officer-only since it removes data
        -- guild-wide for everyone, not just the caller.
        if not IsOfficer(UnitName("player")) then
            Print("Only officers can forget an alt's bank data.")
            return
        end
        if not GuildBankViewerDB.banks[arg] then
            Print("No bank data currently cached for \"" .. arg .. "\".")
            return
        end
        ForgetBankAlt(arg)
        Print("Removed \"" .. arg .. "\" from bank data and told the guild to drop it too.")
        return
    end

    GuildBankViewer_OpenMain()
end

----------------------------------------------------------------------
-- Minimap icon
----------------------------------------------------------------------

function GuildBankViewer_UpdateMinimapVisibility()
    if not GuildBankViewerMinimapButton then return end
    if GuildBankViewerDB.minimapHidden then
        GuildBankViewerMinimapButton:Hide()
    else
        GuildBankViewerMinimapButton:Show()
    end
end

local function UpdateMinimapButtonPosition()
    local angle = math.rad(GuildBankViewerDB.minimapAngle or 200)
    local radius = 80
    local x = math.cos(angle) * radius
    local y = math.sin(angle) * radius
    GuildBankViewerMinimapButton:ClearAllPoints()
    GuildBankViewerMinimapButton:SetPoint("CENTER", Minimap, "CENTER", x, y)
end

local minimapButton = CreateFrame("Button", "GuildBankViewerMinimapButton", Minimap)
minimapButton:SetWidth(31)
minimapButton:SetHeight(31)
minimapButton:SetFrameStrata("MEDIUM")
minimapButton:SetFrameLevel(8)
minimapButton:RegisterForClicks("LeftButtonUp")
minimapButton:RegisterForDrag("LeftButton")

local mmIcon = minimapButton:CreateTexture(nil, "BACKGROUND")
mmIcon:SetWidth(20)
mmIcon:SetHeight(20)
mmIcon:SetTexture("Interface\\Icons\\INV_Misc_Bag_08")
mmIcon:SetPoint("TOPLEFT", 7, -5)

local mmOverlay = minimapButton:CreateTexture(nil, "OVERLAY")
mmOverlay:SetWidth(53)
mmOverlay:SetHeight(53)
mmOverlay:SetTexture("Interface\\Minimap\\MiniMap-TrackingBorder")
mmOverlay:SetPoint("TOPLEFT", 0, 0)

minimapButton:SetScript("OnDragStart", function()
    this:SetScript("OnUpdate", function()
        local mx, my = Minimap:GetCenter()
        local px, py = GetCursorPosition()
        local scale = Minimap:GetEffectiveScale()
        px, py = px / scale, py / scale
        local angle = math.deg(math.atan2(py - my, px - mx))
        GuildBankViewerDB.minimapAngle = angle
        UpdateMinimapButtonPosition()
    end)
end)
minimapButton:SetScript("OnDragStop", function()
    this:SetScript("OnUpdate", nil)
end)

minimapButton:SetScript("OnClick", function()
    GuildBankViewer_OpenMain()
end)

minimapButton:SetScript("OnEnter", function()
    GameTooltip:SetOwner(this, "ANCHOR_LEFT")
    GameTooltip:SetText("Guild Bank Viewer")
    GameTooltip:AddLine("Left-click: open viewer", 1, 1, 1)
    GameTooltip:AddLine("Drag: move this icon", 1, 1, 1)
    GameTooltip:Show()
end)
minimapButton:SetScript("OnLeave", function()
    GameTooltip:Hide()
end)

UpdateMinimapButtonPosition()
if GuildBankViewerDB.minimapHidden then
    minimapButton:Hide()
end
