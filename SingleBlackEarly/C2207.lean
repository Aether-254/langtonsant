import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2207 : checkSingleBlackFast (-90, -71) 22480 .north (47, 43) (-73, -35) = true := by
  decide +kernel

end LangtonsAnt
