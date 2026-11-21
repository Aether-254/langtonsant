import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0503 : checkSingleBlackFast (-5, 1) 5199 .west (-6, 3) (-16, -4) = true := by
  decide +kernel

end LangtonsAnt
