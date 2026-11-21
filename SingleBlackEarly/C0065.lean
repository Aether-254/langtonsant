import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0065 : checkSingleBlackFast (-3, -4) 4779 .west (-5, 3) (-16, -1) = true := by
  decide +kernel

end LangtonsAnt
