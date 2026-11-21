import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1195 : checkSingleBlackFast (26, 4) 11064 .north (-4, 0) (-28, 2) = true := by
  decide +kernel

end LangtonsAnt
