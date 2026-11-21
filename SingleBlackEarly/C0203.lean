import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0203 : checkSingleBlackFast (11, 3) 19763 .west (5, 4) (-27, -21) = true := by
  decide +kernel

end LangtonsAnt
