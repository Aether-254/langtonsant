import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0107 : checkSingleBlackFast (-5, 3) 5051 .west (-7, 3) (-16, -3) = true := by
  decide +kernel

end LangtonsAnt
