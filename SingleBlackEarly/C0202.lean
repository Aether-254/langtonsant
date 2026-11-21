import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0202 : checkSingleBlackFast (11, 4) 5137 .west (-5, 1) (-17, -6) = true := by
  decide +kernel

end LangtonsAnt
