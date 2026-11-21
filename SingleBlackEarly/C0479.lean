import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0479 : checkSingleBlackFast (9, 14) 10489 .west (-5, 0) (-24, -8) = true := by
  decide +kernel

end LangtonsAnt
