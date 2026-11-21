import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0438 : checkSingleBlackFast (17, 6) 23207 .west (3, -4) (-35, -15) = true := by
  decide +kernel

end LangtonsAnt
