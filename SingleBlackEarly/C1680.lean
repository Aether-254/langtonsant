import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1680 : checkSingleBlackFast (-42, -24) 27627 .east (24, 12) (-17, -34) = true := by
  decide +kernel

end LangtonsAnt
