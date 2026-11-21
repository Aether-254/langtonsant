import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2106 : checkSingleBlackFast (-85, -58) 20082 .north (34, 27) (-61, -40) = true := by
  decide +kernel

end LangtonsAnt
