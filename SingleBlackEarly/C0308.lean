import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0308 : checkSingleBlackFast (5, 11) 3235 .west (-3, 2) (-17, -7) = true := by
  decide +kernel

end LangtonsAnt
